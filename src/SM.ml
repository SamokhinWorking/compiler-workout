open GT       
open Language
open List
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config


(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
*)  

let rec eval env config programm  =
  let (stack, stmtConfig) = config in
  let (state, input, output) = stmtConfig in
  match programm with
  | []            -> config
  | instr :: rest -> 
    let evalCode config = eval env config rest in
    let evalJmp config label = eval env config (env#labeled label) in
    match instr with
      | BINOP op   -> evalCode
        (match stack with
        | y :: x :: tail -> ((Expr.evalOperation op x y) :: tail, stmtConfig)
        | _              -> failwith "BINOP"
        )
      | CONST n    -> evalCode (n :: stack, stmtConfig)
      | READ       -> evalCode
        (match input with
        | head :: tail -> (head :: stack, (state, tail, output))
        | _            -> failwith "READ"
        )
      | WRITE       -> evalCode
        (match stack with
        | head :: tail -> (tail, (state, input, output @ [head]))
        | _            -> failwith "WRITE"
        )
      | LD x        -> evalCode (state x :: stack, stmtConfig)
      | ST x        -> evalCode
        (match stack with
        | head :: tail -> (tail, (Expr.update x head state, input, output))
        | _            -> failwith "ST"
        )
      | LABEL _     -> evalCode config
      | JMP l       -> evalJmp config l 
      | CJMP (c, l) ->
        (match stack with
        | head :: tail -> if c = "z" && head = 0 || c = "nz" && head != 0
                          then evalJmp (tail, stmtConfig) l
                          else evalCode config
        | _            -> failwith "CJMP"
)
    
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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o



let compEnv = 
  object (self)
    val mutable label_number = 0

  method generateLabel =
  label_number <- label_number +1;
  ".label"^(string_of_int label_number)

  end

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

let rec compileLabel p lastLabel =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in match p with
  | Stmt.Seq (s1, s2)  ->
    let newLabel = compEnv#generateLabel  in
    let (compiled1, used1) = compileLabel s1 newLabel in
    let (compiled2, used2) = compileLabel s2 lastLabel in
    compiled1 @ (if used1 then [LABEL newLabel] else []) @ compiled2, used2
  | Stmt.Read x        -> [READ; ST x], false
  | Stmt.Write e       -> expr e @ [WRITE], false
  | Stmt.Assign (x, e) -> expr e @ [ST x], false
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
  | Stmt.Repeat (e, s) ->
      let l_repeat = compEnv#generateLabel  in
      let (body, _) = compileLabel s lastLabel in
      [LABEL l_repeat] @ body @ expr e @ [CJMP ("z", l_repeat)], false

let rec compile p =
    let l = compEnv#generateLabel  in
    let compiled, used = compileLabel p l in
compiled @ (if used then [LABEL l] else [])



(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)



