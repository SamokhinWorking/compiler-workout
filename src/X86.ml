open GT
       
(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4;;

(* We need to distinguish the following operand types: *)
@type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)
with show

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string

(* arithmetic correction: decrement                     *) | Dec   of opnd
(* arithmetic correction: or 0x0001                     *) | Or1   of opnd
(* arithmetic correction: shl 1                         *) | Sal1  of opnd
(* arithmetic correction: shr 1                         *) | Sar1  of opnd
(* comment in generated code                            *) | Comment of string 
                                                                                                                                   
(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s
  | Dec    s           -> Printf.sprintf "\tdecl\t%s" (opnd s)
  | Or1    s           -> Printf.sprintf "\torl\t$0x0001,\t%s" (opnd s)
  | Sal1   s           -> Printf.sprintf "\tsall\t%s" (opnd s)
  | Sar1   s           -> Printf.sprintf "\tsarl\t%s" (opnd s)
  | Comment s          -> Printf.sprintf "#%s" s
                                         
(* Opening stack machine to use instructions without fully qualified names *)
open SM

let box value = value * 2 + 1 

let rec range l h = if l >= h then [] else l :: (range (l + 1) h)

 let suffix ops =
      match ops with
        | "<=" -> "le"
        | "<" -> "l"
        | ">=" -> "ge"
        | ">" -> "g"
        | "==" -> "e"
        | "!=" -> "ne"
        | _ -> failwith (Printf.sprintf "Unknown operator %s" ops)

let zero opnd = Binop ("^",opnd,opnd)


(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)


let compile_plus_minus_multiply op l r res =
  let il, ir = l, r in
  let l, r, asm_mov =  match (l, r) with
      | (S _, S _) -> eax, r, [Mov (l, eax)]
      | _ -> l, r, []
   in
     [Sar1 il; Sar1 ir]
   @ asm_mov
   @ [Binop (op, r, l);
     Mov (l, res);]
   @ [Sal1 res; Or1 res]


let compile_div_mod op l r res =
  let pre_res = if op = "/" then eax else edx in
  [Sar1 l; Sar1 r]
 @
  [
    Mov (l, eax);
    zero edx;
    Cltd;
    IDiv r;
    Mov (pre_res, res);
  ]
  @ [Sal1 res; Or1 res]


let compile_cmp op l r res =
  let l, r, asm_mov = match (l, r) with
      | (S _, S _) -> eax, r, [Mov (l, eax)]
      | _ -> l, r, []
  in
  asm_mov 
  @ [
    zero edx;
    Binop ("cmp", r, l);
    Set   (suffix op, "%dl");
    Sal1 edx; Or1 edx;
    Mov   (edx, res)
  ]




let compile_or op l r res = 
  [Sar1 l; Sar1 r]
  @ [
      zero eax;
      Mov (l, edx);
      Binop ("!!", r, edx);
      Set ("nz", "%al");
      Mov (eax, res);
    ]
  @ [Sal1 res; Or1 res]



let compile_and op l r res =
  [Sar1 l; Sar1 r]
  @ [
      zero eax;
      zero edx;
      Binop ("cmp", L 0, l);
      Set ("ne", "%al");
      Binop ("cmp", L 0, r);
      Set ("ne", "%dl");
      Binop ("&&", edx, eax);
      Mov (eax, res);
   ]
  @ [Sal1 res; Or1 res]


let compile_binop op l r res =
  match op with
    | "+" | "-" | "*" -> compile_plus_minus_multiply op l r res
    | "/" | "%" -> compile_div_mod op l r res
    | "<=" | "<" | ">=" | ">" | "==" | "!=" -> compile_cmp op l r res
    | "!!" -> compile_or op l r res
    | "&&" -> compile_and op l r res
    | _ -> failwith ("Unknown operand")



let compile_call env name num_args is_procedure =
  let get_operands env num = (
    let accumulate = (fun (env, operands) _ -> let operand, env = env#pop in (env, operand::operands)) in
    List.fold_left accumulate (env, []) (range 0 num)) in
  let name = match name.[0] with 
    |'.' -> "B" ^ String.sub name 1 (String.length name - 1) 
    | _ -> name in
  let push_regs = List.map (fun reg -> (Push reg)) (env#live_registers num_args) in
  let pop_regs = List.map (fun reg -> (Pop reg)) (env#live_registers num_args) in
  let env, arg_operands = get_operands env num_args in
  let push_args = List.map (fun arg -> Push arg) arg_operands in
  let push_args = match name with 
    | "Barray" -> push_args @ [(Push (L num_args))] 
    | _ -> push_args in
  let env, res_asm = 
    if not is_procedure 
      then let operand, env = env#allocate in env, [Mov (eax, operand)]
      else env, [] in
  env, [Comment "Push regs"] @ push_regs @ 
       [Comment "Push args"] @ push_args @ 
       [Comment "Call"] @ [Call name; Binop ("+", L (word_size * num_args), esp)] @ 
       [Comment "Pop regs"] @ (List.rev pop_regs) @ 
       [Comment "Result"] @ res_asm

let rec compile_single env instr =
  let str_instr = (print_insn instr) in
  let env, asm = match instr with
    | BINOP op -> 
        let r, l, env = env#pop2 in
        let res, env = env#allocate in
        env, (compile_binop op l r res)
    | CONST x ->
      let operand, env = env#allocate in
      env, [Mov (L (box x), operand)]
    | STRING s ->
      let s, env = env#string s in
      let l, env = env#allocate in
      let env, asm = compile_call env ".string" 1 false in
      env, Mov (M ("$" ^ s), l) :: asm
    | SEXP (t, size) ->
      let op_hash, env = env#allocate in
      let op_size, env = env#allocate in
      let env, asm = compile_call env ".sexp" (size + 2) false in
      env, Mov (L size, op_size) :: Mov (L (env#hash t), op_hash) :: asm
    | LD name -> 
      let operand, env = (env#global name)#allocate in
      let var = env#loc name in
      env, [Mov (var, eax); Mov (eax, operand)]
    | ST name -> 
      let operand, env = (env#global name)#pop in
      let var = env#loc name in
      env, [Mov (operand, eax); Mov (eax, var)]
    | STA (name, size) ->
     let asm_mov src dst = match dst with
      | S _ | M _ -> [Mov (src, eax); Mov (eax, dst)]
      | _ -> [Mov (src, dst)] in
      let op_data, env = (env#global name)#allocate in
      let asm_data_mov = asm_mov (env#loc name) op_data in
      let op_size, env = (env#allocate) in
      let env, asm_call = compile_call env ".sta" (size + 2) true in
      env, asm_data_mov @ (Mov (L size, op_size) :: asm_call)
    | LABEL l -> 
      if (env#is_barrier) 
        then (env#drop_barrier)#retrieve_stack l, [Label l]
        else env, [Label l]
    | JMP l -> 
      let env = (env#set_barrier)#set_stack l in 
      env, [Jmp l]
    | CJMP (z, l) ->
      let operand, env = env#pop in
      let env = env#set_stack l in
      env, [Binop ("cmp", L box(0), operand); CJmp (z, l)]
    | DROPJMP (l, size) ->
      let operand, env = env#pop in
      let env = env#set_drop_stack l size in
      env, [Binop ("cmp", L box(0), operand); CJmp ("z", l);]
    | BEGIN (name, args, locals) ->
      let env = env#enter name args locals in
      env, [Push ebp; Mov (esp, ebp)] @ [Binop ("-", M ("$" ^ env#lsize), esp)]
    | END ->
      let return = [Mov (ebp, esp); Pop ebp; Ret; Meta (Printf.sprintf "\t.set %s, %d" env#lsize (env#allocated * word_size))] in
      env, [Label env#epilogue] @ return
    | CALL (name, num_args, is_procedure) ->
      let fname = match name with 
        | "read" -> "Lread" 
        | "write" -> "Lwrite" 
        | "raw" -> "Lraw" 
        | _ -> name in
      compile_call env fname num_args is_procedure
    | RET has_ret ->
      if has_ret
        then let operand, env = env#pop in env, [Mov (operand, eax); Jmp env#epilogue]
        else env, [Jmp env#epilogue]
    | DROP -> let _, env = env#pop in env, []
    | DUP ->
      let asm_mov src dst = match dst with
        | S _ | M _ -> [Mov (src, eax); Mov (eax, dst)]
        | _ -> [Mov (src, dst)] in
      let top = env#peek in
      let dup_op, env = env#allocate in
      env, asm_mov top dup_op
    | SWAP ->
      let top1, top2 = env#peek2 in
      env, [Push top1; Mov (top2, eax); Mov (eax, top1); Pop top2]
    | TAG t ->
      let op_tag, env = env#allocate in
      let env, asm_call = compile_call env ".tag" 2 false in
      env, ((Mov (L (env#hash t), op_tag)) :: asm_call)
    | ENTER locals ->
      let env = env#scope locals in
      let asm_mov_var (env, acc) var =
        let op, env = env#pop in env, (acc @ [Mov (op, env#loc var)]) in
      List.fold_left asm_mov_var (env, []) locals
    | LEAVE -> env#unscope, []
    | _ -> failwith "Unknown SM instruction"
  in 
  env, [Comment str_instr] @ asm

let rec compile env prg = match prg with
  | [] -> env, []
  | instr :: rest ->
    let env, single_asm = compile_single env instr in
    let env, rest_asm = compile env rest in
    env, single_asm @ rest_asm

(* A set of strings *)           
module S = Set.Make (String) 

(* A map indexed by strings *)
module M = Map.Make (String) 

(* Environment implementation *)
class env =
  let chars          = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNJPQRSTUVWXYZ" in
  let make_assoc l i = List.combine l (List.map (fun x -> x + i) (range 0 (List.length l))) in
  let rec assoc  x   = function [] -> raise Not_found | l :: ls -> try List.assoc x l with Not_found -> assoc x ls in
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stringm     = M.empty (* a string map                      *)
    val scount      = 0       (* string count                      *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val static_size = 0       (* static data size                  *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
    val stackmap    = M.empty (* labels to stack map               *)
    val barrier     = false   (* barrier condition                 *)
                        
    method show_stack =
      GT.show(list) (GT.show(opnd)) stack
             
    method print_locals =
      Printf.printf "LOCALS: size = %d\n" static_size;
      List.iter
        (fun l ->
          Printf.printf "(";
          List.iter (fun (a, i) -> Printf.printf "%s=%d " a i) l;
          Printf.printf ")\n"
        ) locals;
      Printf.printf "END LOCALS\n"

    (* check barrier condition *)
    method is_barrier = barrier

    (* set barrier *)
    method set_barrier = {< barrier = true >}

    (* drop barrier *)
    method drop_barrier = {< barrier = false >}
                            
    (* associates a stack to a label *)
    method set_stack l = (*Printf.printf "Setting stack for %s\n" l;*) {< stackmap = M.add l stack stackmap >}
    

    (* associate a stack with dropped <size> values to a label <l> *)
    method set_drop_stack l size =
      let _, stack' = split size stack in {< stackmap = M.add l stack' stackmap >}
                   
    (* retrieves a stack for a label *)
    method retrieve_stack l = (*Printf.printf "Retrieving stack for %s\n" l;*)
      try {< stack = M.find l stackmap >} with Not_found -> self
                               
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
	let rec allocate' = function
	| []                            -> ebx          , 0
	| (S n)::_                      -> S (n+1)      , n+2
	| (R n)::_ when n < num_of_regs -> R (n+1)      , stack_slots
	| _                             -> S static_size, static_size+1
	in
	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* peeks the top of the stack (the stack does not change) *)
    method peek = List.hd stack

    (* peeks two topmost values from the stack (the stack itself does not change) *)
    method peek2 = let x::y::_ = stack in x, y

    (* tag hash: gets a hash for a string tag *)
    method hash tag =
      let h = Pervasives.ref 0 in
      for i = 0 to min (String.length tag - 1) 4 do
        h := (!h lsl 6) lor (String.index chars tag.[i])
      done;
      !h      
             
    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* registers a string constant *)
    method string x =
      try M.find x stringm, self
      with Not_found ->
        let y = Printf.sprintf "string_%d" scount in
        let m = M.add x y stringm in
        y, {< scount = scount + 1; stringm = m>}
                       
    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets all string definitions *)      
    method strings = M.bindings stringm

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      let n = List.length l in
      {< static_size = n; stack_slots = n; stack = []; locals = [make_assoc l 0]; args = make_assoc a 0; fname = f >}

    (* enters a scope *)
    method scope vars =
      let n = List.length vars in
      let static_size' = n + static_size in
      {< stack_slots = max stack_slots static_size'; static_size = static_size'; locals = (make_assoc vars static_size) :: locals >}

    (* leaves a scope *)
    method unscope =
      let n = List.length (List.hd locals) in
      {< static_size = static_size - n; locals = List.tl locals >}
        
    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers depth =
      let rec inner d acc = function
      | []             -> acc
      | (R _ as r)::tl -> inner (d+1) (if d >= depth then (r::acc) else acc) tl
      | _::tl          -> inner (d+1) acc tl
      in
      inner 0 [] stack
       
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Call ("raw", [Language.Expr.Const 0])))) in
   let sm_comp = SM.compile (ds, stmt) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: sm_comp)
  in
  let data = Meta "\t.data" :: (List.map (fun s      -> Meta (Printf.sprintf "%s:\t.int\t0"         s  )) env#globals) @
                               (List.map (fun (s, v) -> Meta (Printf.sprintf "%s:\t.string\t\"%s\"" v s)) env#strings) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
 
