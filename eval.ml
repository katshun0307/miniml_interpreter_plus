open Syntax 
open Core

exception MatchFail

(* 値の定義 *)

(* exval は式を評価して得られる値．dnval は変数と紐付けられる値．今回
   の言語ではこの両者は同じになるが，この2つが異なる言語もある．教科書
   参照． *)
type exval =
  | IntV of int
  | BoolV of bool
  | ProcV of id * exp * dnval Environment.t ref
  | ListProcV of id list * exp * dnval Environment.t ref
  | DProcV of id * exp
  | ListV of exval list
and dnval = exval

exception Error of string

let err s = raise (Error s)

(* pretty printing *)
let rec string_of_exval = function
    IntV i -> string_of_int i
  | BoolV b -> string_of_bool b
  | ProcV _ -> "<fun(´･ω･｀* (⊃⌒＊⌒)>"
  | ListProcV _ -> "<fun>"
  | DProcV _ -> "<dfun>"
  | ListV val_l -> "[" ^ (String.concat ~sep:";" (List.map val_l ~f:string_of_exval)) ^ "]"

let pp_val v = print_string (string_of_exval v)

let rec apply_prim op arg1 arg2 = match op, arg1, arg2 with
    Plus, IntV i1, IntV i2 -> IntV (i1 + i2)
  | Plus, _, _ -> err ("Both arguments must be integer: +")
  | Mult, IntV i1, IntV i2 -> IntV (i1 * i2)
  | Mult, _, _ -> err ("Both arguments must be integer: *")
  | Lt, IntV i1, IntV i2 -> BoolV (i1 < i2)
  | Lt, _, _ -> err ("Both arguments must be integer: <")

let rec find l n = 
  match l with 
  | top :: rest -> if top = n then true else find rest n
  | [] -> false

let multiple_decls_sanity lst = 
  let rec loop l defined = 
    match l with 
    | (id, _) :: rest -> if find defined id then false else loop rest (id :: defined)
    | [] -> true
  in loop lst []

let rec eval_exp env = function
    Var x -> 
    (try Environment.lookup x env with 
       Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | ILit i -> IntV i
  | BLit b -> BoolV b
  | BinOp (op, exp1, exp2) -> 
    let arg1 = eval_exp env exp1 in
    let arg2 = eval_exp env exp2 in
    apply_prim op arg1 arg2
  | LogicOp(op, e1, e2) -> 
    ( match op with 
      | And -> let arg1 = eval_exp env e1 in 
        if arg1 = BoolV(false) then BoolV(false) else 
          let arg2 = eval_exp env e2 in if (arg2 = BoolV(true)) || (arg2 = BoolV(false)) then arg2 else err("non boolean values supplied: &&")
      | Or -> let arg1 = eval_exp env e1 in
        if arg1 = BoolV(true) then BoolV(true) else
          let arg2 = eval_exp env e2 in if (arg2 = BoolV(true)) || (arg2 = BoolV(false)) then arg2 else err("non boolean values supplied: ||"))
  | IfExp (exp1, exp2, exp3) ->
    let test = eval_exp env exp1 in
    (match test with
     | BoolV true -> eval_exp env exp2 
     | BoolV false -> eval_exp env exp3
     | _ -> err ("Test expression must be boolean: if"))
  | MultiLetExp(decls, e) -> 
    if multiple_decls_sanity decls then
      let rec make_env current_env d = 
        (match d with
         | top :: rest -> let (id, e) = top in 
           let v = eval_exp env e in
           let update_env = Environment.extend id v current_env in
           make_env update_env rest
         | [] -> current_env )
      in let eval_env = make_env env decls in
      eval_exp eval_env e
    else err("variable is bound several times")
  | FunExp (params, exp) -> let dummyenv = ref Environment.empty in dummyenv := env;
    ListProcV (params, exp, dummyenv)
  | AppExp (exp1, exp2) -> (
      let funval = eval_exp env exp1 in
      let arg = eval_exp env exp2 in 
      (match funval with 
       (* recurisive function *)
       | ProcV(id, body, env_ref) -> let eval_env = Environment.extend id arg !env_ref in
         eval_exp eval_env body
       (* non-recursive function *)
       | ListProcV (params, body, env_ref) -> (* non-recursive function *)
         (match params with
          | top :: [] -> let newenv = Environment.extend top arg !env_ref in
            eval_exp newenv body
          | top :: rest -> 
            let newenv = Environment.extend top arg !env_ref in
            let dummyenv = ref Environment.empty in
            dummyenv := newenv;
            ListProcV(rest, body, dummyenv)
          | [] -> err("too many arguments"))
       | DProcV(id, body) -> let newenv = Environment.extend id arg env in
         eval_exp newenv body
       | e -> err ("Non function value is applied")))
  | DFunExp (id, exp) -> DProcV(id, exp)
  | LetRecExp (id, para, exp1, exp2) ->
    let dummyenv = ref Environment.empty in
    let newenv = Environment.extend id (ProcV(para, exp1, dummyenv)) env in
    dummyenv := newenv;
    eval_exp newenv exp2
  | ListExp exp_list -> 
    ListV (List.map exp_list ~f:(fun e -> eval_exp env e))
  | MatchExp(case_exp, case_list) -> 
    let case_val = eval_exp env case_exp in
    (match case_val with
     | ListV content_list ->
       let rec loop_cases cases_list =
         (* return dnval if pattern match, else raise Error (MatchFail) *)
         let rec loop_pattern current_case_val return_exp pattern accum_env = 
          (*
          * current_case_val : dnval list : current match target
          * return_exp : expression to evaluate when match succeeds
          * pattern : current pattern trying to match
          * accum env : current environment containing pattern variables
           *)
           match pattern with
           | Cons(hd_id, cons_rest) -> 
             (match current_case_val with
              | h::t -> loop_pattern t return_exp cons_rest (Environment.extend hd_id h accum_env)
              | [] -> raise MatchFail)
           | Id i -> eval_exp (Environment.extend i (ListV current_case_val) accum_env) return_exp
           | Tail -> if current_case_val = [] then eval_exp accum_env return_exp else raise MatchFail
         in
         (* loop through cases *)
         match cases_list with
         | (pattern, e):: rest ->
           (try
              loop_pattern content_list e pattern env
            with MatchFail ->
              loop_cases rest)
         | [] -> raise (Error "does not match any case") in
       loop_cases case_list 
     | _ -> raise (Error "match expression must be applied to list"))


let eval_decl env = function
    Exp e -> let v = eval_exp env e in ("-", env, v)
  | Decl (id, e) -> let v = eval_exp env e in (id, Environment.extend id v env, v)
  | RecDecl(id, para, e) -> (
      let dummyenv = ref Environment.empty in 
      let newenv = Environment.extend id (ProcV(para, e, dummyenv)) env in 
      dummyenv := newenv;
      (id, newenv, ProcV(para, e, dummyenv))
    )
