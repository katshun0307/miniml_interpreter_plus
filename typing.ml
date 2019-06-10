open Syntax
open MySet

exception Error of string
exception MatchNotExhaustive
exception MatchFail

let err s = raise (Error s)

(* type environment *)
type tyenv = tysc Environment.t
type subst = (tyvar * ty) list

(* get list of variant names from user-defined type name *)
let variant_env = ref (Environment.empty: (tyid * ty) list Environment.t)

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
    | TyFloat -> TyFloat
    | TyList t -> TyList (resolve_subst subst_pair t)
    | TyTuple (t1, t2) -> TyTuple(resolve_subst subst_pair t1, resolve_subst subst_pair t2)
    | TyUser id -> TyUser id
    | TyDummy -> TyDummy
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
let rec unify (eqs: (ty * ty) list): (tyvar * ty) list  = 
  let rec loop lst current_subst = 
    (match lst with
     | (x, y) :: rest -> 
       if x = y then loop rest current_subst else
         (match x, y with
          | TyFun(a, b), TyFun(c, d) -> loop ((a, c) :: (b, d) :: rest) current_subst
          | TyVar(id), b | b, TyVar(id) -> 
            if not (MySet.member id (freevar_ty b)) then
              let mid = unify(subst_eqs (id, b) rest) in
              (id, b) :: mid
            else err "unify: could not resolve type"
          | TyTuple(a, b), TyTuple(c, d) ->
            loop ((a, c):: (b, d):: rest) current_subst
          | TyList a, TyList b -> loop ((a, b):: rest) current_subst
          | _ -> err "unify: could not resolve type")
     | _ -> current_subst) in 
  loop eqs []

let ty_prim op (ty1:ty) (ty2:ty) = match op with
  | Plus | Minus | Mult | Div | Modulo -> (TyInt, (ty1, TyInt) :: (ty2, TyInt) :: [])
  | FPlus | FMinus | FMult | FDiv -> (TyFloat, (ty1, TyFloat) :: (ty2, TyFloat) :: [])
  | Lt  -> (TyBool, (ty1, TyInt) :: (ty2, TyInt) :: [])
  | FLt  -> (TyBool, (ty1, TyFloat) :: (ty2, TyFloat) :: [])
  | Eq -> (TyBool, (ty1, ty2) :: [])

let ty_logic op (ty1:ty) (ty2:ty) = 
  match op with
  | And -> (TyBool, (ty1, TyBool) :: (ty2, TyBool) :: [])
  | Or  -> (TyBool, (ty1, TyBool) :: (ty2, TyBool) :: [])

let get_type = function
  | TyVar _ -> "tyvar"
  | TyBool -> "tybool"
  | TyInt -> "tyint"
  | TyFloat -> "tyfloat"
  | TyFun _ -> "tyfun"
  | TyList _ -> "tylist"
  | TyTuple _ -> "tytuple"
  | TyUser ty_name -> ty_name
  | TyDummy -> "dummy"

(* (ex) ['a; int; int 'b] -> [('a, int); (int; int); (int, 'b)] *)
let type_list_to_equals l = 
  let rec loop accum = function
    | t:: [] -> accum
    | hd:: tl -> loop ((hd,(List.hd tl))::accum) tl
    | [] -> raise (Error "entered unexpected case") in
  loop [] l

(* >>> check if pattern matching is exhasutive >>> *)
type match_res = 
  | Match
  | NoMatch
  | Undecidable of match_pattern list

let string_of_match_res = function
  | Match -> "Match"
  | NoMatch -> "NoMatch"
  | Undecidable pl -> 
    "Undecidable["
    ^ Core.String.concat ~sep:"; " (List.map string_of_pattern pl)
    ^ "]"

(* check if ideal pattern matches current pattern. (ideal, current) *)
let rec matches (tyenv: tysc Environment.t) (ideal_p, pp) = 
  (* Printf.printf "match idealp: %s with currentp : %s\n" (string_of_pattern ideal_p) (string_of_pattern pp); *)
  match (ideal_p, pp) with
  | ConsListPattern(iph, ipt), ConsListPattern(ph, pt) -> 
    (match (matches tyenv (iph, ph)), (matches tyenv (ipt, pt)) with
     | Undecidable (_ as l), _ -> Undecidable (List.map (fun a -> ConsListPattern(a, ipt)) l) 
     | _, Undecidable (_ as l) -> Undecidable (List.map (fun a -> ConsListPattern(iph, a)) l)
     | NoMatch, _ | _, NoMatch -> NoMatch
     | Match, Match -> Match )
  | TailListPattern, TailListPattern -> Match
  | TuplePattern(ip1, ip2), TuplePattern(p1, p2) -> 
    (match (matches tyenv (ip1, p1)), (matches tyenv (ip2, p2)) with
     | Undecidable (_ as l), _ -> Undecidable (List.map (fun a -> TuplePattern(a, ip2)) l) 
     | _, Undecidable (_ as l) -> Undecidable (List.map (fun a -> TuplePattern(ip1, a)) l)
     | NoMatch, _ | _, NoMatch -> NoMatch
     | Match, Match -> Match )
  | SingleVariantPattern ityid, SingleVariantPattern tyid -> 
    if tyid = ityid then Match else NoMatch
  | VariantPattern(ityid, ip), VariantPattern(tyid, p) -> 
    if tyid = ityid then
      match matches tyenv (ip, p) with
      | Undecidable exl -> Undecidable (List.map (fun ex -> VariantPattern(tyid, ex)) exl)
      | _ as res -> res
    else NoMatch
  | _, IdPattern _ -> Match
  | IdPattern _, ConsListPattern _ | IdPattern _, TailListPattern ->
    Undecidable [ConsListPattern(IdPattern "_", TailListPattern); TailListPattern]
  | IdPattern _, SingleVariantPattern tyid -> 
    let tysc_of_variant = Environment.lookup tyid tyenv in
    (match ty_of_tysc tysc_of_variant with
     | TyUser tt -> 
       let variant_list = Environment.lookup tt (!variant_env) in
       Undecidable (List.map (fun (tyid, _) -> SingleVariantPattern tyid) variant_list)
     | _ -> err ("cannot find type of single variant : " ^ tyid))
  | IdPattern _, VariantPattern(tyid, _) -> 
    let tysc_of_variant = Environment.lookup tyid tyenv in
    (match ty_of_tysc tysc_of_variant with
       TyFun(_, TyUser tt) -> 
       let variant_list = Environment.lookup tt (!variant_env) in
       Undecidable (List.map (fun (tyid, _) -> VariantPattern (tyid, IdPattern "_")) variant_list)
     | _ -> err ("cannot find type of variant : " ^ tyid))
  | IdPattern _, TuplePattern _ -> Undecidable [TuplePattern(IdPattern "_", IdPattern "_")]
  | _, UnderbarPattern -> Match
  | _ -> NoMatch

let pattern_same_var_check pattern_list = 
  let rec loop p accum = 
    let open Core in
    match p with
    | ConsListPattern (p1, p2) | TuplePattern(p1, p2) -> 
      let _, p1_accum = loop p1 accum in
      loop p2 p1_accum
    | TailListPattern | SingleVariantPattern _ -> true, accum
    | VariantPattern (_, p1) -> loop p1 accum
    | IdPattern i -> 
      not (MySet.exists i accum), MySet.insert i accum
    | UnderbarPattern -> true, accum
  in List.iter (fun (pp, _) -> 
      try 
        let valid, _ = loop pp [] in assert valid
      with _ -> err "match variable must not be same") pattern_list

let check_pattern_exhaustive tyenv pattern_list = 
  let rec sigma ideal_pattern patterns = 
    let open Core in
    let match_flags = Core.List.map patterns ~f:(fun p -> matches tyenv (ideal_pattern, p)) in
    (* Printf.printf "flags are [%s]\n" (String.concat ~sep:"; " (List.map ~f:string_of_match_res match_flags)); *)
    if Core.List.exists match_flags ~f:((=) Match)
    then ()
    else if Core.List.for_all match_flags ~f:((=) NoMatch)
    then
      (Printf.eprintf "Pattern matching not exhaustive, cannot match pattern: ";
       Printf.eprintf "%s" (string_of_pattern ideal_pattern ^ "\n");
       raise MatchNotExhaustive)
    else 
      let rec loop_match_flags current_flags = 
        match current_flags with
        | Undecidable extends::_ -> 
          List.iter ~f:(fun i -> sigma i patterns) extends
        | _::rest_flags -> loop_match_flags rest_flags
        | [] -> err "Undecidable does not exist" in
      loop_match_flags match_flags in
  sigma (IdPattern "_") pattern_list
(* <<< check if pattern matching is exhasutive <<< *)

let rec ty_exp tyenv = function
  | Var (ID x) | Var (VARIANT x) -> 
    (try
       let TyScheme(vars, ty) = Environment.lookup x tyenv in
       let s = List.map (fun id -> (id, TyVar(fresh_tyvar ()))) vars in
       (tysc_of_ty(subst_type s ty), [])
     with Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | ILit _ -> (tysc_of_ty(TyInt), [])
  | BLit _ -> (tysc_of_ty(TyBool), [])
  | FLit _ -> (tysc_of_ty(TyFloat), [])
  | Float_of_int e1 -> 
    let tysc1, tysubst1 = ty_exp tyenv e1 in
    let equals = (TyInt, ty_of_tysc tysc1) :: (eqls_of_subst tysubst1) in
    let main_subst = unify equals in
    (tysc_of_ty TyFloat, main_subst)
  | Int_of_float e1 -> 
    let tysc1, tysubst1 = ty_exp tyenv e1 in
    let equals = (TyFloat, ty_of_tysc tysc1) :: (eqls_of_subst tysubst1) in
    let main_subst = unify equals in
    (tysc_of_ty TyInt, main_subst)
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
    pattern_same_var_check case_list;
    let rec extend_pattern_env p cty (accum_tyenv: tysc Environment.t) accum_eqls =
      (* Printf.printf "pattern is %s and type is %s\n" (string_of_pattern p) (string_of_ty cty); *)
      match p, cty with
      | ConsListPattern(p1, p2), TyList lty ->
        let p1_tyenv, eqls' = extend_pattern_env p1 lty accum_tyenv accum_eqls in
        extend_pattern_env p2 (TyList lty) p1_tyenv eqls'
      | TailListPattern, TyList _ -> accum_tyenv, accum_eqls
      | TuplePattern (p1, p2), TyTuple(ty1, ty2) -> 
        let p1_tyenv, eqls' = extend_pattern_env p1 ty1 accum_tyenv accum_eqls in
        extend_pattern_env p2 ty2 p1_tyenv eqls'
      | SingleVariantPattern pt_tyid, TyUser ty_id -> accum_tyenv, accum_eqls
      | VariantPattern(pt_tyid, ipt), TyUser ty_id ->
        (* pt_tyid is Yogurt, ty_id is food *)
        let pt_tyscname = Environment.lookup pt_tyid tyenv in
        let pt_ty = ty_of_tysc pt_tyscname in
        (match pt_ty with
         | TyFun(pt_tyconstructor, TyUser pt_tyname) -> 
           extend_pattern_env ipt pt_tyconstructor accum_tyenv accum_eqls
         | _ -> err "error in match")
      | IdPattern id, (_ as tt) -> 
        if id = "_" then accum_tyenv, accum_eqls
        else
          Environment.extend id (tysc_of_ty tt) accum_tyenv, accum_eqls
      | UnderbarPattern, _ -> accum_tyenv, accum_eqls
      | ConsListPattern(p1, p2), TyVar tid -> 
        let new_tv = fresh_tyvar () in
        let eqls' = (cty, TyList (TyVar new_tv)):: accum_eqls in
        let p1_tyenv, p1_eqls = extend_pattern_env p1 (TyVar new_tv) accum_tyenv eqls' in
        extend_pattern_env p2 (TyList (TyVar new_tv)) p1_tyenv p1_eqls
      | TailListPattern, TyVar _ -> accum_tyenv, accum_eqls
      | TuplePattern(p1, p2), TyVar _ -> 
        let new_tv1 = TyVar (fresh_tyvar ()) in
        let new_tv2 = TyVar (fresh_tyvar ()) in
        let eqls' = (cty, TyTuple(new_tv1, new_tv2)):: accum_eqls in
        let p1_tyenv, p1_eqls = extend_pattern_env p1 new_tv1 accum_tyenv eqls' in
        extend_pattern_env p2 new_tv2 p1_tyenv p1_eqls
      | SingleVariantPattern _, TyVar _ -> accum_tyenv, accum_eqls
      | VariantPattern (pt_tyid, ipt), TyVar _ -> 
        (* pt_tyid is Yogurt, ty_id is food *)
        let pt_tyscname = Environment.lookup pt_tyid tyenv in
        let pt_ty = ty_of_tysc pt_tyscname in
        let pt_constructor = match pt_ty with
          | TyFun(pt_tyconstructor, TyUser pt_tyname) -> 
            pt_tyconstructor
          | _ -> err "error in match" in
        extend_pattern_env ipt pt_constructor accum_tyenv accum_eqls
      | _ -> raise MatchFail in
    (* check pattern exhaustive *)
    check_pattern_exhaustive tyenv (Core.List.map case_list ~f:(fun(p, _) -> p));
    (* loop through match patterns making eqls conditions *)
    let return_ty = TyVar(fresh_tyvar ()) in
    let rec loop_cases l eqls = 
      (* loop through cases *)
      (match l with
       | (pt, e):: tl -> 
         let extended_tyenv, extended_eqls = extend_pattern_env pt (ty_of_tysc case_tysc) tyenv [] in
         (* print_string (string_of_eqls extended_eqls ^ "\n"); *)
         let e_tysc, e_subst = ty_exp extended_tyenv e in
         (* Printf.printf "got %s as e_tysc\n" (string_of_tysc e_tysc); *)
         loop_cases tl ((ty_of_tysc e_tysc, return_ty)::(eqls_of_subst e_subst) @ extended_eqls @ eqls)
       | [] -> eqls) in 
    let main_eqls = loop_cases case_list [] in
    (* Printf.printf "got main_eqls as %s\n" (string_of_eqls main_eqls); *)
    let main_subst = unify main_eqls in
    (tysc_of_ty (subst_type main_subst return_ty), main_subst)
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
    let e_ty, _ = ty_decl tyenv (Exp e)  in
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
  | TypeDecl(type_name, variant_list) ->
    let rec append_tyenv l accum_tyenv = 
      match l with
      | (variant, TyDummy)::t -> 
        let accum_tyenv' =  Environment.extend variant (tysc_of_ty (TyUser type_name)) accum_tyenv in
        append_tyenv t accum_tyenv'
      | (variant, construct_ty)::t -> 
        let accum_tyenv' =  Environment.extend variant (tysc_of_ty (TyFun(construct_ty, TyUser type_name))) accum_tyenv in
        append_tyenv t accum_tyenv'
      | [] -> accum_tyenv in
    variant_env := Environment.extend type_name variant_list !variant_env;
    let new_tyenv = append_tyenv variant_list tyenv in
    (tysc_of_ty TyDummy, new_tyenv)
