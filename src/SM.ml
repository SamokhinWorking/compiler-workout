open GT    
open Syntax
  
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)  
let evalInstr (stack, (state, input, output)) prg = match  prg with
	| BINOP op -> (match stack with 
		| y::x::tail -> ((Expr.evalOperation op x y)::tail, (state,input,output))
		| _ -> failwith "BINOP")
	| CONST z -> (z::stack, (state, input,output))
	| READ -> (match input with
		| z::tail -> (z::stack, (state,tail,output))
		| _ -> failwith "READ")
	| WRITE -> (match stack with
		| z::tail -> (tail,(state,input,output @ [z]))
		| _ -> failwith "WRITE")
	| LD x -> ((state x)::stack, (state, input,output))
	| ST x -> (match stack with
		| z::tail -> (tail,(Expr.update x z state, input, output))
		| _ -> failwith "ST")
		
			
(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)

let eval config prg = List.fold_left evalInstr config prg
	


let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compileExpr e = match e with
	| Expr.Const c -> [CONST c]
	| Expr.Var v -> [LD v]
	| Expr.Binop (op,l,r) -> (compileExpr l) @ (compileExpr r) @ [BINOP op]

let rec compile stmt = match stmt with
	| Stmt.Read v -> [READ; ST v]
	| Stmt.Write e -> (compileExpr e) @ [WRITE]
	| Stmt.Assign (v,e) -> ( compileExpr e) @ [ST v]
	| Stmt.Seq(e1,e2) -> (compile e1) @ (compile e2)


