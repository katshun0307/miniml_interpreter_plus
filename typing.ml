open Syntax
open MySet

exception Error of string
exception MatchNotExhaustive

let err s = raise (Error s)

(* type environment *)
type tyenv = tysc Environment.t
type subst = (tyvar * ty) list

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
    | TyTuple (t1, t2) -> TyTuple(resolve_subst subst_pair t1, resolve_subst subst_pair t2)
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

(* free type variables in the current environment *)
let rec freevar_tyenv (tyenv: tyenv) = 
  let freevars = Core.List.map tyenv ~f:(fun (_, scm) -> freevar_tysc scm) in
  List.concat freevars

let closure ty tyenv subst = 
  (* fv_tyenv' : free (unbound) variables in current tyenv *)
  let fv_tyenv' = freevar_tyenv tyenv in
  (* fv_tyenv : 環境中の自由型変数のうち, 型が定まらない(型変数)であるもの. *)
  (* つまり, 現在の情報で型付けできない型変数 *)
  let fv_tyenv = 
    MySet.bigunion
      (MySet.map
         (fun id -> freevar_ty (subst_type subst (TyVar id)))
         fv_tyenv') in
  (* ty 中の自由型変数から, 現在型付けできなかった型環境中の型変数を除いたもの. *)
  let ids = MySet.diff (freevar_ty ty) fv_tyenv in
  TyScheme (MySet.to_list ids, ty)

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
  | TyTuple _ -> "tytuple"

(* (ex) ['a; int; int 'b] -> [('a, int); (int; int); (int, 'b)] *)
let type_list_to_equals l = 
  let rec loop accum = function
    | t:: [] -> accum
    | hd:: tl -> loop ((hd,(List.hd tl))::accum) tl
    | [] -> raise (Error "entered unexpected case") in
  loop [] l

(* >>> check if pattern matching is exhasutive >>> *)

(* exhaustive pattern checking *)
type match_res = 
  | Match
  | NoMatch
  | Undecidable

(* substitute last pattern id with tail 
   ex) a::b::c --> a::b::[] *)
let rec subst_tail = function
  | Cons(a, rest) ->  Cons(a, subst_tail rest)
  | Tail -> Tail
  | Id _ -> Tail

(* check if ideal pattern matches current pattern. (ideal, current) *)
let rec matches = function 
  | Cons(_, rest), Cons(_, rest2) -> matches (rest, rest2)
  | Tail, Tail | _, Id _ -> Match
  | Cons(_, _), Tail | Tail, Cons(_, _) -> NoMatch
  | Id _, Tail | Id _, Cons(_, _) -> Undecidable

(* pattern exhaustivity checking for single list match *)
let check_pattern_exhaustive pattern_list =
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
      (Printf.eprintf "Pattern matching not exhaustive, cannot match pattern: ";
       Printf.eprintf "%s" (string_of_list_pattern ideal_pattern ^ "\n");
       raise MatchNotExhaustive)
  in
  sigma (Id "_") pattern_list

(* pattern exhaustivity checking for tuple list match *)
let check_multi_pattern_exhaustive pattern_tuple_list = 
  let rec sigma ((ideal_pattern1, ideal_pattern2): (list_pattern * list_pattern)) (patterns: (list_pattern * list_pattern) list) =
    let match_flags = Core.List.map patterns ~f:(fun (p1, p2) -> 
        let m1 = matches (ideal_pattern1, p1) in
        let m2 = matches (ideal_pattern2, p2) in (m1, m2)) in
    if Core.List.exists match_flags ~f:(fun x -> x = (Match, Match)) 
    then  () (* there is a match *)
    else if Core.List.exists match_flags ~f:(fun (x1, x2) -> x1 = Undecidable)
    then (* nothing decidable:increment the ideal pattern *)
      (sigma (subst_tail ideal_pattern1, ideal_pattern2) patterns;
       sigma (Cons("_", ideal_pattern1), ideal_pattern2) patterns)
    else if Core.List.exists match_flags ~f:(fun (x1, x2) -> x2 = Undecidable)
    then
      (sigma (ideal_pattern1, subst_tail ideal_pattern2) patterns;
       sigma (ideal_pattern1, Cons("_", ideal_pattern2)) patterns)
    else (* there is no match *)    
      (Printf.eprintf "Pattern matching not exhaustive, cannot match pattern: ";
       Printf.eprintf "%s" ("(" ^ string_of_list_pattern ideal_pattern1 ^ ", " ^ string_of_list_pattern ideal_pattern2 ^ ")\n");
       raise MatchNotExhaustive) in
  sigma (Id "_", Id "_") pattern_tuple_list

(* <<< check if pattern matching is exhasutive <<< *)

let rec ty_exp tyenv = function
  | Var x -> 
    (try
       let TyScheme(vars, ty) = Environment.lookup x tyenv in
       let s = List.map (fun id -> (id, TyVar(fresh_tyvar ()))) vars in
       (tysc_of_ty(subst_type s ty), [])
     with Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | ILit _ -> (tysc_of_ty(TyInt), [])
  | BLit _ -> (tysc_of_ty(TyBool), [])
  | BinOp (op, exp1, exp2) -> 
    let tyarg1, tysubst1 = ty_exp tyenv exp1 in
    let tyarg2, tysubst2 = ty_exp tyenv exp2 in
    let ty3, eqs3 = ty_prim op (ty_of_tysc tyarg1) (ty_of_tysc tyarg2) in
    let eqs = (eqls_of_subst tysubst1) @ (eqls_of_subst tysubst2) @ eqs3 in
    let main_subst = unify eqs in
    (tysc_of_ty ty3, main_subst)
  | LogicOp(op, exp1, exp2) -> 
    (let tyarg1, tysubst1 = ty_exp tyenv exp1 in
     let tyarg2, tysubst2 = ty_exp tyenv exp2 in
     let ty3, eqs3 = ty_logic op (ty_of_tysc tyarg1) (ty_of_tysc tyarg2) in
     let eqs = (eqls_of_subst tysubst1) @ (eqls_of_subst tysubst2) @ eqs3 in
     let main_subst = unify eqs in (tysc_of_ty ty3, main_subst))
  | IfExp (exp1, exp2, exp3) -> 
    let tyarg1, tysubst1 = ty_exp tyenv exp1 in
    let cond_type = get_type (ty_of_tysc tyarg1) in
    (* if condition part is valid *)
    if cond_type = "tybool" || cond_type = "tyvar" then
      let new_eqs = (ty_of_tysc tyarg1, TyBool) :: eqls_of_subst tysubst1 in
      let tyarg2, tysubst2 = ty_exp tyenv exp2 in
      let tyarg3, tysubst3 = ty_exp tyenv exp3 in
      let main_subst = unify ((eqls_of_subst tysubst2) @ (eqls_of_subst tysubst3) @ new_eqs @ [(ty_of_tysc tyarg2, ty_of_tysc tyarg3)]) in
      (tysc_of_ty (subst_type main_subst (ty_of_tysc tyarg2)), main_subst)
    else err "condition must be boolean: if"
  | MultiLetExp (params, exp) -> 
    (* let x = 3 in x;;
       MultiLetExp([(x, 3)], x) *)
    let rec extend_envs_from_list (current_tyenv:tyenv) current_subst current_para_types p =
      (* current_tyenv: accumulates and adds param sets (id and values) to tyenv
         current_subst: accumulates substitutions produced when evaluating param types
         current_para_types : accumulates all the types of params for poly-let *)
      match p with
      | (id, e) :: rest -> 
        let e_tysc, e_subst = ty_exp tyenv e in
        let tysc' = closure (ty_of_tysc e_tysc) tyenv e_subst in
        let new_tyenv = Environment.extend id tysc' current_tyenv in
        let new_subst = current_subst @ e_subst in
        extend_envs_from_list new_tyenv new_subst (e_tysc::current_para_types) rest
      | [] -> current_tyenv, current_subst, current_para_types in
    let eval_tyenv, eval_subst, para_types = extend_envs_from_list tyenv [] [] params in
    let exp_ty, exp_subst = ty_exp eval_tyenv exp in
    let main_subst = unify (eqls_of_subst eval_subst @ eqls_of_subst exp_subst) in
    (tysc_of_ty (subst_type main_subst (ty_of_tysc exp_ty)), main_subst)
  | FunExp(params, exp) ->
    let rec extend_envs_from_list (current_env:tyenv) p =
      (* get environment with new tyvar for each params to evaluate the main function *)
      (match p with
       | id :: rest ->
         let new_tyvar = fresh_tyvar() in
         let new_env = Environment.extend id (TyScheme([], TyVar new_tyvar)) current_env in
         extend_envs_from_list new_env rest
       | [] -> current_env ) in
    let eval_tyenv = extend_envs_from_list tyenv params in
    (* evaluate main function in the created environment *)
    let res_ty, res_tysubst = ty_exp eval_tyenv exp in
    (* find arguments with undecided type (tyvar) *)
    let find_poly_vars param_ids = 
      let rec loop vl accum = 
        match vl with
        | v:: rest -> 
          (match subst_type res_tysubst v with
           | TyVar tv -> loop rest (tv::accum)
           | _ -> loop rest accum)
        | [] -> accum in
      loop (List.map (fun i -> ty_of_tysc(Environment.lookup i eval_tyenv)) param_ids) [] in
    (* make output ( re-evaluate args ) *)
    let rec eval_type p e =
      (match p with
       | top :: rest ->
         (try
            let arg_tyvar = Environment.lookup top eval_tyenv in
            let arg_ty = subst_type res_tysubst (ty_of_tysc arg_tyvar) in
            TyFun(arg_ty, eval_type rest e)
          with _ -> err "error in fun exp")
       | [] -> subst_type res_tysubst e) in
    let main_ty = eval_type params (ty_of_tysc res_ty) in
    let unbound_vars = find_poly_vars params in
    (TyScheme(unbound_vars, main_ty), res_tysubst)
  | AppExp(exp1, exp2) ->
    let ty_exp1, tysubst1 = ty_exp tyenv exp1 in
    let ty_exp2, tysubst2 = ty_exp tyenv exp2 in
    (* make new var *)
    let ty_ret = TyVar(fresh_tyvar()) in
    let subst_main = unify([ty_of_tysc ty_exp1, TyFun(ty_of_tysc ty_exp2, ty_ret)] @ eqls_of_subst tysubst1 @ eqls_of_subst tysubst2) in
    let ty_3 = subst_type subst_main ty_ret in
    (tysc_of_ty ty_3, subst_main)
  | LetRecExp(id, para, e1, e2) -> 
    let ty_ret = TyVar(fresh_tyvar()) in (* type of return value: f x *)
    let ty_para = TyVar(fresh_tyvar()) in (* type of parameter: x *)
    (* first formula *)
    (* >>> make env *)
    let eval_tyenv1 = Environment.extend id (tysc_of_ty (TyFun(ty_para, ty_ret))) (Environment.extend para (tysc_of_ty ty_para) tyenv) in
    let (TyScheme(e1_bounds, e1_ty)), e1_subst = ty_exp eval_tyenv1 e1 in
    let first_subst = unify((ty_ret, e1_ty) :: eqls_of_subst e1_subst) in
    let ty_para_eval = subst_type first_subst ty_para in
    let ty_x_eval = subst_type first_subst ty_ret in
    (* second formula *)
    (* >>> make env *)
    let let_fun = match subst_type first_subst ty_para with
      | TyVar tv -> TyScheme(tv::e1_bounds, TyFun(ty_para_eval, ty_x_eval))
      | _ -> TyScheme(e1_bounds, TyFun(ty_para_eval, ty_x_eval)) in
    let eval_tyenv2 = Environment.extend id let_fun tyenv in
    (* >>> eval and unify *)
    let e2_ty, e2_subst = ty_exp eval_tyenv2 e2 in
    let main_subst = unify((e1_ty, ty_ret) ::eqls_of_subst e1_subst @ eqls_of_subst e2_subst) in
    (tysc_of_ty (subst_type main_subst (ty_of_tysc e2_ty)), main_subst)
  | MatchExp (case_exp, case_list) -> 
    let case_tysc, case_subst = ty_exp tyenv case_exp in
    let rec extend_list_patten_env p accum_env list_ty ids =
      match p with
      | Cons(hd_id, rest_pattern) ->
        if List.exists ((=) hd_id) ids 
        then raise (Error "match variable must not be same") 
        else
          extend_list_patten_env rest_pattern (Environment.extend hd_id (tysc_of_ty list_ty) accum_env) list_ty (hd_id:: ids)
      | Tail -> accum_env
      | Id id -> if List.exists ((=) id) ids 
        then raise (Error "match variable must not be same") 
        else Environment.extend id (tysc_of_ty (TyList list_ty)) accum_env in
    (match ty_of_tysc case_tysc with
     | TyList list_ty -> 
       (* check pattern exhaustive *)
       check_pattern_exhaustive (Core.List.map case_list ~f:(fun(p, _) -> 
           match p with | ListPattern pp -> pp | _ -> raise (Error "error at pattern exhaustivity check")));
       let return_ty = TyVar (fresh_tyvar ()) in
       (* loop through match patterns making eqls conditions *)
       let rec loop_cases l eqls_cases = 
         (* loop through cases *)
         (match l with
          | (ListPattern matchcase, e):: tl -> 
            let extended_tyenv = extend_list_patten_env matchcase tyenv list_ty [] in
            let e_tysc, e_subst = ty_exp extended_tyenv e in
            loop_cases tl ((ty_of_tysc e_tysc, return_ty)::(eqls_of_subst e_subst) @ eqls_cases)
          | (TuplePattern _, _):: _ -> 
            raise (Error "unexpected pattern") 
          | [] -> eqls_cases) in 
       let eqls = loop_cases case_list [] in
       let main_subst =  unify eqls in
       (tysc_of_ty (subst_type main_subst return_ty), main_subst)
     | TyTuple(TyList list_ty1, TyList list_ty2) -> 
       (* check pattern exhaustive *)
       check_multi_pattern_exhaustive (Core.List.map case_list ~f:(fun (pt, _) ->
           match pt with |  TuplePattern(pp1, pp2) -> (pp1, pp2) | _ -> raise (Error "error at pattern exhaustivity check") ));
       let rec return_ty = TyVar (fresh_tyvar ()) in
       let rec loop_cases l eqls_cases = 
         (match l with
          | (TuplePattern (pattern1, pattern2), e):: tl -> 
            let extended_tyenv = extend_list_patten_env pattern1 (extend_list_patten_env pattern2 tyenv list_ty2 []) list_ty1 [] in
            let e_tysc, e_subst = ty_exp extended_tyenv e in
            loop_cases tl ((ty_of_tysc e_tysc, return_ty)::(eqls_of_subst e_subst) @ eqls_cases)
          | (ListPattern _, _):: _ -> 
            raise (Error "unexpected pattern") 
          | [] -> eqls_cases) in 
       let eqls = loop_cases case_list [] in
       let main_subst = unify eqls in
       (tysc_of_ty (subst_type main_subst return_ty), main_subst)
     | _ -> raise (Error "match expression must be for lists"))
  | ListExp expl -> 
    let list_ty = TyVar (fresh_tyvar ()) in
    let rec generate_lsteqls l accum = 
      (match l with
       | hd :: [] -> 
         let hdtysc, _ = ty_exp tyenv hd in
         (list_ty, ty_of_tysc hdtysc) ::accum
       | hd:: tl -> 
         let hdtysc, _ = ty_exp tyenv hd in
         let tltysc, _ = ty_exp tyenv (List.hd tl) in
         generate_lsteqls tl ((ty_of_tysc hdtysc, ty_of_tysc tltysc):: accum)
       | [] -> accum
      ) in
    let eqls = generate_lsteqls expl [] in
    let main_subst = unify eqls in
    (tysc_of_ty (TyList (subst_type main_subst list_ty)), main_subst) 
  | TupleExp(e1, e2) -> 
    let tysc1, ty_subst1 = ty_exp tyenv e1 in
    let tysc2, ty_subst2 = ty_exp tyenv e2 in
    let main_subst = unify (eqls_of_subst ty_subst1 @ eqls_of_subst ty_subst2) in
    let main_ty = TyTuple(subst_type main_subst (ty_of_tysc tysc1),subst_type main_subst (ty_of_tysc tysc2)) in
    (tysc_of_ty main_ty, [])
  | _ -> err "ty_exp: not implemented"

let rec ty_decl (tyenv: tyenv) = function
  | Exp e -> 
    let (type_, _) = ty_exp tyenv e in
    (type_, tyenv)
  | Decl(id, e) -> 
    let e_ty, _ = ty_decl tyenv (Exp e) in
    let new_tyenv = Environment.extend id (closure (ty_of_tysc e_ty) tyenv []) tyenv in
    (e_ty, new_tyenv)
  | RecDecl (id, para, e) -> 
    let ty_x = TyVar(fresh_tyvar()) in (* type of return value: f x *)
    let ty_para = TyVar(fresh_tyvar()) in (* type of parameter: x *)
    let eval_tyenv = Environment.extend id (tysc_of_ty (TyFun(ty_para, ty_x))) (Environment.extend para (tysc_of_ty ty_para) tyenv) in
    let tysc_main, e_subst = ty_exp eval_tyenv e in
    let main_subst = unify( (ty_x, ty_of_tysc tysc_main) :: eqls_of_subst e_subst) in
    let ty_para2 = subst_type main_subst ty_para in
    let main_ty = TyFun(ty_para2, ty_of_tysc tysc_main) in
    (tysc_of_ty main_ty, Environment.extend id (tysc_of_ty main_ty) tyenv)
