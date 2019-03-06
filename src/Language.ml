(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (*Convert int to bool*)
    let intToBool var = var != 0
    (*Convert bool to int*)
    let boolToInt var = if var then 1 else 0 
    (* int->int-> bool to int -> int -> int *)
    let compareInt f var1 var2 = boolToInt ( f var1 var2 )
    (*bool -> bool_-> bool to int-> int-> int *)
    let compareBool f var1 var2 = boolToInt (f (intToBool var1) (intToBool var2 ) )
    (*Convert operator to Ocaml*)
    let evalOperation op = match op with
      | "+"  -> ( + )
      | "-"  -> ( - )
      | "*"  -> ( * )
      | "/"  -> ( / )
      | "%"  -> ( mod ) 
      | "<"  -> compareInt( < )
      | ">"  -> compareInt( > )
      | "<=" -> compareInt( <= )
      | ">=" -> compareInt( >= )
      | "==" -> compareInt( = )
      | "!=" -> compareInt( <> )
      | "&&" -> compareBool( && )
      | "!!" -> compareBool( || )
      | _    -> failwith "Unknown operator" ;;


    (* Expression evaluator

         val eval : state -> expr -> int
     
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)

    let rec eval state expr = match expr with
      | Const var -> var 
      | Var str -> state str
      | Binop (op, expr1, expr2) -> evalOperation op (eval state expr1) (eval state expr2) 



    let parseBinop op = ostap(- $(op)),(fun expr1 expr2 -> Binop (op,expr1,expr2))

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
      expr:
        !(Ostap.Util.expr
          (fun x-> x)
          (Array.map (fun (assoc,op) -> assoc,List.map parseBinop op)
            [|
              `Lefta, ["!!"];
              `Lefta, ["&&"];
              `Nona,  ["<=";"<";">=";">";"!=";"==";];
              `Lefta, ["+";"-"];
              `Lefta, ["*";"/";"%"];
            |]
          )
          primary
        );
      primary: x:IDENT {Var x}| c:DECIMAL {Const c}| -"(" expr -")"
    )

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
 
    let rec eval (state,input,output) stmt = match stmt with
    | Read x -> (match input with
		| z::tail ->(Expr.update x z state, tail, output)
		| _ -> failwith "Read")
    | Write e -> (state,input,output @ [Expr.eval state e])
    | Assign (x,e)-> (Expr.update x (Expr.eval state e) state, input,output)
    | Seq (e1,e2) -> eval (eval (state,input,output) e1) e2

    (* Statement parser *)
    ostap (
      stmt : "read"  "("  x:IDENT ")"          { Read x }
           | "write" "("  exp:!(Expr.expr) ")" { Write exp }
           | x:IDENT ":=" exp:!(Expr.expr)     { Assign (x,exp) };

      parse: line:stmt ";" rest:parse {Seq (line,rest)} | stmt
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
