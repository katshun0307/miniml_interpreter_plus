open Syntax 
open Core

exception MatchFail
exception SameVarError

(* 値の定義 *)

(* exval は式を評価して得られる値．dnval は変数と紐付けられる値. *)
type exval =
  | IntV of int
  | BoolV of bool
  | StringV of string
  | ProcV of id * exp * dnval Environment.t ref
  | ListProcV of id list * exp * dnval Environment.t ref
  | DProcV of id * exp
  | ListV of exval list
  | TupleV of exval * exval
  | UserV of id * exval
and dnval = exval

exception Error of string

let err s = raise (Error s)

(* pretty printing *)
let rec string_of_exval = function
    IntV i -> string_of_int i
  | BoolV b -> string_of_bool b
  | StringV s -> s 
  | ProcV _ -> "<fun(´･ω･｀* (⊃⌒＊⌒)>"
  | ListProcV _ -> "<fun>"
  | DProcV _ -> "<dfun>"
  | ListV val_l -> "[" ^ (String.concat ~sep:";" (List.map val_l ~f:string_of_exval)) ^ "]"
  | TupleV (v1, v2) -> "(" ^ string_of_exval v1 ^ ", " ^ string_of_exval v2 ^ ")"
  | UserV (id, v) -> id ^ " " ^ string_of_exval v

let pp_val v = print_string (string_of_exval v)

let rec check_equals = function
  | IntV i1, IntV i2 -> i1 = i2
  | BoolV i1, BoolV i2 -> i1 = i2
  | StringV s1, StringV s2  -> s1 = s2
  | UserV(s1, _), UserV (s2, _) -> s1 = s2
  | ListV l1, ListV l2 -> 
    (try 
       List.fold2_exn l1 l2 ~init:true ~f:(fun x y z -> x && check_equals (y, z))
     with _ -> false)
  | TupleV (u1, u2), TupleV (v1, v2) -> 
    check_equals (u1, v1) && check_equals (u2, v2)
  | _ -> err ("Both arguments must be value: =")

let rec apply_prim op arg1 arg2 = match op, arg1, arg2 with
  | Plus, IntV i1, IntV i2 -> IntV (i1 + i2)
  | Plus, _, _ -> err ("Both arguments must be integer: +")
  | Minus, IntV i1, IntV i2 -> IntV (i1 - i2)
  | Minus, _, _ -> err ("Both arguments must be integer: -")
  | Mult, IntV i1, IntV i2 -> IntV (i1 * i2)
  | Mult, _, _ -> err ("Both arguments must be integer: *")
  | Div, IntV i1, IntV i2 -> IntV (i1 / i2)
  | Div, _, _ -> err ("Both arguments must be integer: /")
  | Lt, IntV i1, IntV i2 -> BoolV (i1 < i2)
  | Lt, _, _ -> err ("Both arguments must be integer: <")
  | Modulo, IntV i1, IntV i2 -> IntV (i1 % i2)
  | Modulo, _, _ -> err ("Both arguments must be integer: %")
  | Eq, _, _ -> BoolV (check_equals (arg1, arg2))

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
  | SLit s -> StringV s
  | BinOp (op, exp1, exp2) -> 
    let arg1 = eval_exp env exp1 in
    let arg2 = eval_exp env exp2 in
    apply_prim op arg1 arg2
  | LogicOp(op, e1, e2) -> 
    ( match op with 
      | And -> let arg1 = eval_exp env e1 in 
        if arg1 = BoolV(false) then BoolV(false) else 
          let arg2 = eval_exp env e2 in 
          if (arg2 = BoolV(true)) || (arg2 = BoolV(false)) 
          then arg2 
          else err("non boolean values supplied: &&")
      | Or -> let arg1 = eval_exp env e1 in
        if arg1 = BoolV(true) then BoolV(true) else
          let arg2 = eval_exp env e2 in 
          if (arg2 = BoolV(true)) || (arg2 = BoolV(false)) 
          then arg2 
          else err("non boolean values supplied: ||"))
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
  | LetRecExp (id, (para_id, para_hint), exp1, exp2) ->
    let dummyenv = ref Environment.empty in
    let newenv = Environment.extend id (ProcV(para_id, exp1, dummyenv)) env in
    dummyenv := newenv;
    eval_exp newenv exp2
  | ListExp exp_list -> 
    ListV (List.map exp_list ~f:(fun e -> eval_exp env e))
  | MatchExp(guard_exp, pattern_list) -> 
    let rec make_env list_pattern current_case accum_env =
      match list_pattern, current_case with
      | Cons(hd_id, rest_pattern), hd::tl -> 
        make_env rest_pattern tl (Environment.extend hd_id hd accum_env)
      | Id id, _ -> 
        Environment.extend id (ListV current_case) accum_env
      | Tail, [] -> accum_env
      | _ -> raise MatchFail in
    let guard_val = eval_exp env guard_exp in
    (match guard_val with
     (* guard_val is list *)
     | ListV content_list ->
       let rec loop_pattern current_pattern_list = 
         match current_pattern_list with
         | (ListPattern p, e):: rest ->
           (try
              let eval_env = make_env p content_list env in
              eval_exp eval_env e
            with MatchFail ->
              loop_pattern rest)
         | (_, _):: _ -> raise (Error "does not match any case") 
         | [] -> raise (Error "does not match any case") in
       loop_pattern pattern_list 
     (* guard_val is tuple *)
     | TupleV (ListV content_list1, ListV content_list2) -> 
       let rec loop_pattern current_pattern_list  = 
         match current_pattern_list with
         | (TuplePattern (p1, p2), e)::rest ->
           (try
              let env_p1 = make_env p1 content_list1 env in
              let env_p2 = make_env p2 content_list2 env_p1 in
              eval_exp env_p2 e
            with MatchFail -> loop_pattern rest)
         | _ -> raise (Error "does not match any case") in
       loop_pattern pattern_list
     | _ -> raise (Error "match expression must be applied to list"))
  | TupleExp(e1, e2) -> TupleV(eval_exp env e1, eval_exp env e2)

let eval_decl env = function
    Exp e -> let v = eval_exp env e in ("-", env, v)
  | Decl ((id, _), e) -> let v = eval_exp env e in (id, Environment.extend id v env, v)
  | RecDecl(id, para, e) -> (
      let dummyenv = ref Environment.empty in 
      let newenv = Environment.extend id (ProcV(para, e, dummyenv)) env in 
      dummyenv := newenv;
      (id, newenv, ProcV(para, e, dummyenv)))
