open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
       
let rec eval env config programm  =
  let (controlStack,stack, stmtConfig) = config in
  let (state, input, output) = stmtConfig in
  match programm with
  | []            -> config
  | instr :: rest -> 
    let evalCode config = eval env config rest in
    let evalJmp config label = eval env config (env#labeled label) in
    match instr with
      | BINOP op   -> evalCode
        (match stack with
        | y :: x :: tail -> (controlStack,(Value.of_int (Expr.to_func op (*Expr.operate op *) (Value.to_int x) (Value.to_int y))) :: tail, stmtConfig)
        | _              -> failwith "BINOP"
        )
      | CONST n    -> evalCode (controlStack, (Value.of_int n) :: stack, stmtConfig)
      | STRING s -> evalCode (controlStack, (Value.of_string s) :: stack, stmtConfig)
      | LD x        -> evalCode (controlStack, State.eval state x :: stack, stmtConfig)
      | ST x        -> evalCode
        (match stack with
        | head :: tail -> (controlStack, tail, (State.update x head state, input, output))
        | _            -> failwith "ST"
        )
      | STA (n, s) -> 
        let (value::idxs), stack' = split (s + 1) stack in
        evalCode(controlStack,stack', (Stmt.update state n value idxs, input, output))
      | LABEL _           -> evalCode config
      | JMP l             -> evalJmp config l
      | CJMP (c, l)       ->
      (match stack with
      | head :: tail -> if c = "z" && (Value.to_int head)==0 || c = "nz" &&  (Value.to_int head )!=0
                        then  eval env (controlStack, tail, stmtConfig) (env#labeled l) 
                        else  eval env (controlStack, tail, stmtConfig) rest 
      | _            -> failwith "CJMP"
      )
      | BEGIN (_,a, loc) -> 
                        let stateWithScope = State.enter state (a @ loc) in
                        let restore = List.map (fun p -> ST p) a in
                        let cfg' = eval env (controlStack, stack, (stateWithScope, input, output)) restore in
                        eval env cfg' rest

      
      | CALL (f,arg_cnt, is_func) -> if env#is_label f
                                    then eval env ((rest, state) :: controlStack, stack, stmtConfig) (env#labeled f)
                                    else eval env (env#builtin config f arg_cnt (not is_func)) rest
      | (RET _ | END) -> match controlStack with 
        | (rest,oldState) :: tail ->
           let newStmtConfig = (State.leave state oldState, input,output) in
           let newConfig = (tail,stack,newStmtConfig) in
           eval env newConfig rest
        | _ -> config
      


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o



let compEnv = 
  object (self)
    val mutable label_number = 0

  method generateLabel =
  label_number <- label_number +1;
  ".label"^(string_of_int label_number)

  end

let rec compileLabel p lastLabel =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.String s ->  [STRING s]
  | Expr.Elem (a,i) -> expr a @ expr i @ [CALL ("$elem", 2, true)]
  | Expr.Length n -> expr n @ [CALL ("$length", 1, true)]
  | Expr.Array a ->  exprList (List.rev a) @ [CALL ("$array", List.length a, true)]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (f, args)   ->exprList args @ [CALL (f, List.length args, true)]
    and exprList es = List.fold_left (fun acc e -> expr e @ acc) [] es
  in match p with
  | Stmt.Seq (s1, s2)  ->
    let newLabel = compEnv#generateLabel  in
    let (compiled1, used1) = compileLabel s1 newLabel in
    let (compiled2, used2) = compileLabel s2 lastLabel in
    compiled1 @ (if used1 then [LABEL newLabel] else []) @ compiled2, used2

  | Stmt.Assign (x, idxs, e) -> (match idxs with
    | [] -> expr e @ [ST x], false
    | _ ->  exprList idxs @ expr e @ [STA (x, List.length idxs)], false
  )
  | Stmt.Skip          -> [], false
  | Stmt.If (e, s1, s2)  ->
    let l_else = compEnv#generateLabel  in
    let (if_body, used1) = compileLabel s1 lastLabel in
    let (else_body, used2) = compileLabel s2 lastLabel in
    expr e @ [CJMP ("z", l_else)] @ if_body @ (if used1 then [] else [JMP lastLabel]) @ [LABEL l_else] @ else_body @ (if used2 then [] else [JMP lastLabel]), true
  | Stmt.While (e, s)  ->
    let check = compEnv#generateLabel  in
    let loop = compEnv#generateLabel in
    let (body, _) = compileLabel s check in
    [JMP check; LABEL loop] @ body @ [LABEL check] @ expr e @ [CJMP ("nz", loop)], false
  | Stmt.Repeat (s, e) ->
    let l_repeat = compEnv#generateLabel  in
    let (body, _) = compileLabel s lastLabel in
    [LABEL l_repeat] @ body @ expr e @ [CJMP ("z", l_repeat)], false
  | Stmt.Call (f,args) ->
  
   let compiled_args = List.fold_left (fun ilist arg -> ilist @ (expr arg)) [] args in
   compiled_args @ [CALL (f, List.length args, false)],false
  | Stmt.Return e -> (match e with
    | Some x -> (expr x) @[ RET true]
    | _ -> [RET false]),false



let rec compileMain p =
    let l = compEnv#generateLabel  in
    let compiled, used = compileLabel p l in
    compiled @ (if used then [LABEL l] else [])

let rec compileDefs defs =
    List.fold_left (fun (p) (name,(args,locals,body)) ->
      let body = compileMain body in
      p @ [LABEL name] @ [BEGIN (name,args,locals)] @ body @ [END]) [] defs


let rec compile(defs,main)=
  let stm = compileMain main in
  let def = compileDefs defs in
  stm @ [END] @ def
