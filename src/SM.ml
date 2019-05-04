open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
(* drop values from stack and jmp  *) | ZJMPDROP of string * int
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
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
         let evalInstr = function 
          | BINOP op   -> 
            (match stack with
            | y :: x :: tail -> ( (Value.of_int (Expr.to_func op  (Value.to_int x) (Value.to_int y))) :: tail, stmtConfig)
            | _              -> failwith "BINOP"
            )
          | CONST n    -> ( (Value.of_int n) :: stack, stmtConfig)
          | STRING x        -> ((Value.of_string (Bytes.of_string x)) :: stack, stmtConfig)
          | LD x            -> (State.eval state x :: stack, (state, input, output))
          | ST x            -> (List.tl stack, (Language.State.update x (List.hd stack) state, input, output))
          | STA (n, s)      ->
              let (value::idxs, tail) = split (s+ 1) stack in
              (tail, (Stmt.update state n value (List.rev idxs), input, output))
          | SEXP (tag, cnt) -> 
              let values, stack' = split cnt stack in
              ((Value.sexp tag @@ (List.rev values))::stack', stmtConfig)
          | DROP            -> (List.tl stack, stmtConfig)
          | DUP             -> (List.hd stack :: stack, stmtConfig)
          | SWAP            -> let x::y::stack' = stack in (y::x::stack', stmtConfig)
          | TAG t           ->
              let x::stack' = stack in
              let res = match x with
                  | Value.Sexp (t', _) -> if (t = t') then 1 else 0
                  | _                  -> 0 in
              ((Value.of_int res)::stack', stmtConfig)
          | BEGIN (_, params, locals) ->
              let state' = Language.State.enter state (params @ locals) in
              let values, stack' = split (List.length params) stack in
              let state'' = List.fold_left (fun s (x, v) -> State.update x v s) state' (List.combine params @@ List.rev values) in
              (stack', (state'', input, output))
          | LABEL l         -> (stack, stmtConfig)
          | ENTER args       ->
              let values, stack' = split (List.length args) stack in
              (stack', (State.push state (List.fold_left (fun s (x, v) -> State.bind x v s) State.undefined (List.combine args values)) args, input, output))
          | LEAVE           -> (stack, (State.drop state, input, output))
      in
      match programm with
          | []           -> config
          | JMP l       :: _ -> eval env config (env#labeled l)
          | CJMP (z, l) :: p ->
              let v = Value.to_int (List.hd stack) in
              let b = if z = "z" then v == 0 else v != 0 in
              if b then eval env (controlStack, List.tl stack, stmtConfig) (env#labeled l)
              else eval env (controlStack, List.tl stack, stmtConfig) p
          | CALL (f, n, fl)   :: p ->
            if env#is_label f 
            then eval env ((p, state)::controlStack, stack, stmtConfig) (env#labeled f)
            else eval env (env#builtin (controlStack, stack, stmtConfig) f n fl) p
          | (RET _  | END)   :: _ -> (match controlStack with
              | (p, oldState)::tail -> eval env (tail, stack, (Language.State.leave state oldState, input, output)) p
              | _ -> (controlStack, stack, stmtConfig))
          | ZJMPDROP (l, cnt) :: p ->
              let z::stack = stack in
              if Value.to_int z = 0
              then let (_,  stack') = split cnt stack in eval env (controlStack, stack', stmtConfig) (env#labeled l)
              else eval env (controlStack, stack, stmtConfig) p
          | x :: p ->
              let (stack, stmtConfig) = evalInstr x in
          eval env (controlStack, stack, stmtConfig) p
       
    


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
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
           (*Printf.printf "Builtin:\n";*)
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

let rec match_pattern lFalse depth = function
  | Stmt.Pattern.Wildcard | Stmt.Pattern.Ident _ -> false, [DROP]
  | Stmt.Pattern.Sexp (t, ps) -> true, [TAG t] @ [ZJMPDROP (lFalse, depth)] @
    (List.flatten @@ List.mapi (fun i p -> [DUP; CONST i; CALL (".elem", 2, false)] @
        (match p with
        | Stmt.Pattern.Sexp (_, ps') ->
            if List.length ps' > 0 then [DUP] @ snd (match_pattern lFalse (depth + 1) p) @ [DROP]
            else snd (match_pattern lFalse depth p)
        | _ -> snd (match_pattern lFalse depth p))
      ) ps)

let rec make_bindings p =
  let rec inner p' = match p' with
    | Stmt.Pattern.Wildcard -> []
    | Stmt.Pattern.Ident var -> [[]]
    | Stmt.Pattern.Sexp (_, xs) ->
       let next i x = List.map (fun arr -> i::arr) (inner x) in
       List.flatten (List.mapi next xs) in
  let topElem i = [CONST i; CALL (".elem", 2, false)] in
  let extractBindValue path = [DUP] @ (List.flatten (List.map topElem path)) @ [SWAP] in
List.flatten (List.map extractBindValue (List.rev (inner p)))

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compileLabel p lastLabel =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.String n         -> [STRING n]
  | Expr.Array a          ->
    let compiled = List.flatten (List.map expr a) in
    compiled @ [CALL (".array", (List.length compiled), false)]
  | Expr.Elem (a, i)      -> expr a @ expr i @ [CALL (".elem", 2, false)]
  | Expr.Length n         -> expr n @ [CALL (".length", 1, false)]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (f, args) ->
    let compileArgs = List.flatten @@ List.map expr args in
    compileArgs @ [CALL (f, List.length args, false)]
  | Expr.Sexp (t, xs)     ->
    let compiled = List.flatten (List.map expr xs) in
    compiled @ [SEXP (t, List.length xs)]
  in match p with
  | Stmt.Seq (s1, s2)  ->
    let newLabel = compEnv#generateLabel  in
    let (compiled1, used1) = compileLabel s1 newLabel in
    let (compiled2, used2) = compileLabel s2 lastLabel in
    compiled1 @ (if used1 then [LABEL newLabel] else []) @ compiled2, used2
  | Stmt.Assign (x, [], e) -> (expr e @ [ST x]), false
  | Stmt.Assign (x, idx, e) -> List.flatten (List.map expr (idx @ [e])) @ [STA (x, List.length idx)], false
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
  | Stmt.Call (f, args) ->
    let compile_args = List.flatten @@ List.map expr args in
    compile_args @ [CALL (f, List.length args, true)], false
  | Stmt.Return e -> (match e with
    | Some x -> (expr x) @[ RET true]
    | _ -> [RET false]),false
  | Stmt.Leave -> [LEAVE], false
  | Stmt.Case (e, [p, s]) -> 
    let pUsed, pCode = match_pattern lastLabel 0 p in
    let sBody, sUsed = compileLabel (Stmt.Seq (s, Stmt.Leave)) lastLabel in
    expr e @ [DUP] @ pCode @ make_bindings p @ [DROP; ENTER (List.rev (Stmt.Pattern.vars p))] @ sBody, pUsed || sUsed
  | Stmt.Case (e, bs)      ->
    let n = List.length bs - 1 in
    let _, _, code = List.fold_left
        (fun (l, i, code) (p, s) ->
            let lFalse, jmp = if i = n then lastLabel, []
                else compEnv#generateLabel, [JMP lastLabel] in
             let _, pCode = match_pattern lFalse 0 p in
             let sBody, _ = compileLabel (Stmt.Seq (s, Stmt.Leave)) lastLabel in
             let amLabel = match l with Some x -> [LABEL x; DUP] | None -> [] in
             (Some lFalse, i + 1, (amLabel @ pCode @ make_bindings p @ [DROP; ENTER (List.rev (Stmt.Pattern.vars p))] @ sBody @ jmp) :: code)
                ) (None, 0, []) bs in
    expr e @ [DUP] @ List.flatten @@ List.rev code, true



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
