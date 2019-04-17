open Syntax
open MySet
(* open Core *)

exception Error of string
exception MatchNotExhaustive

let err s = raise (Error s)

(* type environment *)
type tyenv = ty Environment.t
type subst = (tyvar * ty) list

(* exhaustive pattern checking *)
type match_res = 
  | Match
  | NoMatch
  | Undecidable

(* printing *)
let rec string_of_subst = function 
  | (id, ty) :: rest -> "(" ^ string_of_ty (TyVar(id)) ^ ", " ^ string_of_ty ty ^ ")" ^ string_of_subst rest
  | [] -> ""

let rec string_of_eqs = function 
  | (ty1, ty2) :: rest -> "(" ^ string_of_ty ty1 ^ ", " ^ string_of_ty ty2 ^ ")" ^ string_of_eqs rest
  | _ -> ""

(* apply subst:(substutution) to ty:(type) *)
let rec subst_type s ty = 
  let rec resolve_subst (subst_tyvar, subst_ty) ty = 
    let subst_pair = (subst_tyvar, subst_ty) in
    match ty with
    | TyVar id -> if id = subst_tyvar then subst_ty else TyVar id
    | TyFun(a, b) -> TyFun(resolve_subst subst_pair a, resolve_subst subst_pair b)
    | TyInt -> TyInt
    | TyBool -> TyBool
    | TyList t -> TyList (resolve_subst subst_pair t)
  in match s with 
  | top :: rest -> 
    subst_type rest (resolve_subst top ty)
  | [] -> ty

(* reform subst(substitution) to eql:(list of equal types) *)
let eqls_of_subst subst =  
  let reform sub = 
    let ((id: tyvar), (t: ty)) = sub in 
    (TyVar id, t) in
  List.map reform subst

(* apply subst:(substitution) to eql:(list of equal types) *)
let subst_eqs subst eql = 
  List.map (fun (t1, t2) -> (subst_type [subst] t1, subst_type [subst] t2)) eql

(* main unification algorithm *)
let rec unify eqs: (tyvar * ty) list  = 
  let rec loop lst current_subst = 
    (match lst with
     | (x, y) :: rest -> 
       if x = y then loop rest current_subst else
         (match x, y with
          | TyFun(a, b), TyFun(c, d) -> loop ((a, c) :: (b, d) :: rest) current_subst
          | TyVar(id), b -> 
            if not (MySet.member id (freevar_ty b)) then
              let mid = unify(subst_eqs (id, b) rest) in
              (id, b):: mid
            else err "unify: could not resolve type"
          | b, TyVar(id) -> 
            if not (MySet.member id (freevar_ty b)) then
              let mid = unify(subst_eqs (id, b) rest) in
              (id, b) :: mid
            else err "unify: could not resolve type"
          | _ -> err "unify: could not resolve type"
         )
     | _ -> current_subst) in 
  loop eqs []

let ty_prim op (ty1:ty) (ty2:ty) = match op with
  | Plus -> (TyInt, (ty1, TyInt) :: (ty2, TyInt) :: [])
  | Mult -> (TyInt, (ty1, TyInt) :: (ty2, TyInt) :: [])
  | Lt  -> (TyBool, (ty1, TyInt) :: (ty2, TyInt) :: [])

let ty_logic op (ty1:ty) (ty2:ty) = 
  match op with
  | And -> (TyBool, (ty1, TyBool) :: (ty2, TyBool) :: [])
  | Or  -> (TyBool, (ty1, TyBool) :: (ty2, TyBool) :: [])

let get_type = function
  | TyVar _ -> "tyvar"
  | TyBool -> "tybool"
  | TyInt -> "tyint"
  | TyFun _ -> "tyfun"   
  | TyList _ -> "tylist"

(* (ex) ['a; int; int 'b] -> [('a, int); (int; int); (int, 'b)] *)
let type_list_to_equals l = 
  let rec loop accum = function
    | t:: [] -> accum
    | hd:: tl -> loop ((hd,(List.hd tl))::accum) tl
    | [] -> raise (Error "entered unexpected case") in
  loop [] l

(* check is pattern matching is exhasutive *)
let rec subst_tail = function
  | Cons(a, rest) ->  Cons(a, subst_tail rest)
  | Tail -> Tail
  | Id _ -> Tail

let check_pattern_exhaustive pattern_list =
  (* check ideal pattern matches current pattern. (ideal, current) *)
  let rec matches = function 
    | Cons(_, rest), Cons(_, rest2) -> matches (rest, rest2)
    | Tail, Tail | _, Id _ -> Match
    | Cons(_, _), Tail | Tail, Cons(_, _) -> NoMatch
    | Id _, Tail | Id _, Cons(_, _) -> Undecidable in
  let rec sigma ideal_pattern patterns =
    let match_flags = Core.List.map patterns ~f:(fun p -> matches (ideal_pattern, p)) in
    if Core.List.exists match_flags ~f:(fun x -> x = Match) 
    then (* there is a match *)
      ()
    else if Core.List.exists match_flags ~f:(fun x -> x = Undecidable)
    then (* nothing decidable:increment the ideal pattern *)
      (sigma (subst_tail ideal_pattern) patterns;
       sigma (Cons("a", ideal_pattern)) patterns)
    else (* there is no match *)
      raise MatchNotExhaustive
  in
  sigma (Id "_") pattern_list

let rec ty_exp tyenv = function
  | Var x -> 
    (try (Environment.lookup x tyenv, []) with 
       Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | ILit _ -> (TyInt, [])
  | BLit _ -> (TyBool, [])
  | BinOp (op, exp1, exp2) -> 
    let tyarg1, tysubst1 = ty_exp tyenv exp1 in
    let tyarg2, tysubst2 = ty_exp tyenv exp2 in
    let ty3, eqs3 = ty_prim op tyarg1 tyarg2 in
    let eqs = (eqls_of_subst tysubst1) @ (eqls_of_subst tysubst2) @ eqs3 in
    let main_subst = unify eqs in
    (ty3, main_subst)
  | LogicOp(op, exp1, exp2) -> 
    (let tyarg1, tysubst1 = ty_exp tyenv exp1 in
     let tyarg2, tysubst2 = ty_exp tyenv exp2 in
     let ty3, eqs3 = ty_logic op tyarg1 tyarg2 in
     let eqs = (eqls_of_subst tysubst1) @ (eqls_of_subst tysubst2) @ eqs3 in
     let main_subst = unify eqs in (ty3, main_subst))
  | IfExp (exp1, exp2, exp3) -> 
    let tyarg1, tysubst1 = ty_exp tyenv exp1 in
    let cond_type = get_type tyarg1 in
    (* if condition part is valid *)
    if cond_type = "tybool" || cond_type = "tyvar" then
      let new_eqs = (tyarg1, TyBool) :: eqls_of_subst tysubst1 in
      let tyarg2, tysubst2 = ty_exp tyenv exp2 in
      let tyarg3, tysubst3 = ty_exp tyenv exp3 in
      let main_subst = unify ((eqls_of_subst tysubst2) @ (eqls_of_subst tysubst3) @ new_eqs @ [(tyarg2, tyarg3)]) in
      (subst_type main_subst tyarg2, main_subst)
    else err "condition must be boolean: if"
  | MultiLetExp (params, exp) -> 
    let rec extend_envs_from_list current_tyenv current_subst p =
      match p with
      | (id, e) :: rest -> 
        let e_type, e_subst = ty_exp tyenv e in
        let new_tyenv = Environment.extend id e_type current_tyenv in
        let new_subst = current_subst @ e_subst in
        extend_envs_from_list new_tyenv new_subst rest
      | [] -> current_tyenv, current_subst in
    let eval_tyenv, eval_subst = extend_envs_from_list tyenv [] params in
    let exp_ty, exp_subst = ty_exp eval_tyenv exp in
    let main_subst = unify (eqls_of_subst eval_subst @ eqls_of_subst exp_subst) in
    (subst_type main_subst exp_ty, main_subst)
  | FunExp(params, exp) ->
    let rec extend_envs_from_list current_env p =
      (match p with
       | id :: rest ->
         let new_tyvar = TyVar (fresh_tyvar()) in
         let new_env = Environment.extend id new_tyvar current_env in
         extend_envs_from_list new_env rest
       | [] -> current_env ) in
    (* get environment with new tyvar for each params to evaluate the main function *)
    let eval_tyenv = extend_envs_from_list tyenv params in
    (* evaluate main function in the created environment *)
    let res_ty, res_tysubst = ty_exp eval_tyenv exp in
    (* make output ( re-evaluate args ) *)
    let rec eval_type p e =
      (match p with
       | top :: rest ->
         (try
            let arg_tyvar = Environment.lookup top eval_tyenv in
            let arg_ty =  subst_type res_tysubst arg_tyvar in
            TyFun(arg_ty, eval_type rest e)
          with _ -> err "error in fun exp")
       | [] -> e) in
    (eval_type params res_ty, res_tysubst)
  | AppExp(exp1, exp2) ->
    let ty_exp1, tysubst1 = ty_exp tyenv exp1 in
    let ty_exp2, tysubst2 = ty_exp tyenv exp2 in
    (* make new var *)
    let ty_x = TyVar(fresh_tyvar()) in
    let subst_main = unify([ty_exp1, TyFun(ty_exp2, ty_x)] @ eqls_of_subst tysubst1 @ eqls_of_subst tysubst2) in
    let ty_3 = subst_type subst_main ty_x in
    (ty_3, subst_main)
  | LetRecExp(id, para, e1, e2) -> 
    let ty_x = TyVar(fresh_tyvar()) in (* type of return value: f x *)
    let ty_para = TyVar(fresh_tyvar()) in (* type of parameter: x *)
    (* first formula *)
    let eval_tyenv1 = Environment.extend id (TyFun(ty_para, ty_x)) (Environment.extend para ty_para tyenv) in
    let e1_ty, e1_subst = ty_exp eval_tyenv1 e1 in
    (* let first_subst = unify((ty_x, e1_ty) :: eqls_of_subst e1_subst) in *)
    (* second formula *)
    let eval_tyenv2 = Environment.extend id (TyFun(ty_para, ty_x)) tyenv in
    let e2_ty, e2_subst = ty_exp eval_tyenv2 e2 in
    (* unify all eqls *)
    let main_subst = unify( (e1_ty, ty_x) ::eqls_of_subst e1_subst @ eqls_of_subst e2_subst) in
    (subst_type main_subst e2_ty, main_subst)
  | MatchExp (case_exp, case_list) -> 
    let case_ty, case_subst = ty_exp tyenv case_exp in
    (* check pattern exhaustive *)
    check_pattern_exhaustive (Core.List.map case_list ~f:(fun(p, _) -> p));
    (match case_ty with
     | TyList list_ty -> 
       let return_ty = TyVar (fresh_tyvar ()) in
       (* loop through match patterns making eqls conditions *)
       let rec loop_cases l eqls_cases = 
         (* make type environment for a single match pattern *)
         let rec make_case_env case accum_env = 
           (match case with
            | Cons(hd_id, next) -> 
              make_case_env next (Environment.extend hd_id list_ty accum_env)  
            | Id i -> (Environment.extend i (TyList list_ty) accum_env)
            | Tail -> tyenv
           ) (* end of make_case_env *)
         in
         (* loop through cases *)
         (match l with
          | (matchcase, e):: tl -> 
            let e_ty, e_subst = ty_exp (make_case_env matchcase tyenv) e in
            loop_cases tl ((e_ty, return_ty)::(eqls_of_subst e_subst) @ eqls_cases)
          | [] -> eqls_cases) in 
       let eqls = loop_cases case_list [] in
       let main_subst =  unify eqls in
       (subst_type main_subst return_ty, main_subst)
     | _ -> raise (Error "match expression must be for lists"))
  | ListExp expl -> 
    let list_ty = TyVar (fresh_tyvar ()) in
    let rec generate_lsteqls l accum = 
      (match l with
       | hd :: [] -> 
         let hdty, _ = ty_exp tyenv hd in
         (list_ty, hdty) ::accum
       | hd:: tl -> 
         let hdty, _ = ty_exp tyenv hd in
         let tlty, _ = ty_exp tyenv (List.hd tl) in
         generate_lsteqls tl ((hdty, tlty):: accum)
       | [] -> accum
      ) in
    let eqls = generate_lsteqls expl [] in
    let main_subst = unify eqls in
    (TyList (subst_type main_subst list_ty), main_subst) 
  | _ -> err "ty_exp: not implemented"

let rec ty_decl tyenv = function
  | Exp e -> 
    let (type_, _) = ty_exp tyenv e in
    (type_, tyenv)
  | Decl(id, e) -> 
    let e_ty, _ = ty_decl tyenv (Exp e) in
    let new_tyenv = Environment.extend id e_ty tyenv in
    (e_ty, new_tyenv)
  | RecDecl (id, para, e) -> 
    let ty_x = TyVar(fresh_tyvar()) in (* type of return value: f x *)
    let ty_para = TyVar(fresh_tyvar()) in (* type of parameter: x *)
    let eval_tyenv = Environment.extend id (TyFun(ty_para, ty_x)) (Environment.extend para ty_para tyenv) in
    let ty_main, e_subst = ty_exp eval_tyenv e in
    let main_subst = unify( (ty_x, ty_main) :: eqls_of_subst e_subst) in
    let ty_para2 = subst_type main_subst ty_para in
    let main_ty = TyFun(ty_para2, ty_main) in
    (main_ty, Environment.extend id main_ty tyenv)
(* | _ -> err "not implemented" *)
