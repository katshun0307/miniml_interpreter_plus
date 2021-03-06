open Syntax 
open Core

exception MatchFail
exception SameVarError
exception Error of string
let err s = raise (Error s)

(* 値の定義 *)
type location = int

let fresh_location = 
  let counter = ref 0 in
  let body = 
    fun () -> 
      let v = !counter in
      counter := v + 1; v in
  body

(* exval は式を評価して得られる値．dnval は変数と紐付けられる値. *)
type exval =
  | IntV of int
  | BoolV of bool
  | FloatV of float
  | ProcV of id * exp * dnval Environment.t ref
  | ListProcV of annot_id list * exp * dnval Environment.t ref
  | DProcV of id * exp
  | ListV of exval list
  | TupleV of exval * exval
  | UserV of tyid
  | VariantDefV of string option * id * ((id * ty) list)
  | ArityUserV of tyid
  | ArityAppUserV of tyid * exval
  | RecordV of id * ((id * exval ref * bool) list)
  | RecordDefV of string option * id * ((id * ty * bool) list)
  | RefV of location
  | UnitV
and dnval = exval

let loc_mapping = ref ([]: (int * exval) list)

let append_loc loc v = 
  loc_mapping := List.Assoc.add !loc_mapping ~equal:(=) loc v

let lookup_loc loc = 
  match List.Assoc.find !loc_mapping ~equal:(=) loc with
  | Some x -> x
  | None -> err "no value mapped to location"

(* pretty printing *)
let rec string_of_exval = function
    IntV i -> string_of_int i
  | BoolV b -> string_of_bool b
  | FloatV f -> string_of_float f
  | ProcV _ -> "<fun(´･ω･｀* (⊃⌒＊⌒)>"
  | ListProcV _ -> "<fun>"
  | DProcV _ -> "<dfun>"
  | ListV val_l -> "[" ^ (String.concat ~sep:";" (List.map val_l ~f:string_of_exval)) ^ "]"
  | TupleV (v1, v2) -> "(" ^ string_of_exval v1 ^ ", " ^ string_of_exval v2 ^ ")"
  | UserV tyid -> tyid
  | ArityUserV tyid -> tyid
  | ArityAppUserV (tyid, v) -> tyid ^ " " ^ (string_of_exval v)
  | RecordV (recname, contentlist) -> 
    "{" ^ Core.String.concat ~sep:"; " (List.map ~f:(fun (fname, fcontent, is_mut) -> 
        let mut_str = if is_mut then "mutable " else "" in
        mut_str ^ fname ^ "=" ^ (string_of_exval !fcontent)) contentlist ) ^ "}"
  | RecordDefV (tyarg_opt, recname, fl) ->
    let tyarg_tyvar = Option.value_map tyarg_opt ~f:fresh_tyvar_annot ~default:0 in
    let tyarg_str = Option.value tyarg_opt ~default:"" in
    "type " ^ tyarg_str ^ " " ^ recname ^ " = {" ^ 
    (String.concat ~sep:"; " (List.map ~f:(fun (fname, fty, is_mutable) -> 
         let mut_str = if is_mutable then "mutable " else "" in
         mut_str ^ fname ^ " : " ^ (string_of_ty ~tyvar_str:[(tyarg_tyvar, tyarg_str)] fty)) fl))
    ^ "}"
  | VariantDefV(tyarg_opt, tyname, variant_list) -> 
    let tyarg_tyvar = Option.value_map tyarg_opt ~f:fresh_tyvar_annot ~default:0 in
    let tyarg_str = Option.value tyarg_opt ~default:"" in
    "type " ^ tyarg_str ^ " " ^ tyname ^ " = " ^ 
    String.concat ~sep:"| "
      (List.map variant_list ~f:(fun (variant_id, content_ty) ->
           variant_id ^ " of " ^ (string_of_ty ~tyvar_str:[(tyarg_tyvar, tyarg_str)] content_ty)))  
  | RefV loc -> sprintf "{contents = %s}" (string_of_exval (lookup_loc loc))
  | UnitV -> "()"

let pp_val v = print_string (string_of_exval v)

let rec check_equals = function
  | IntV i1, IntV i2 -> i1 = i2
  | BoolV i1, BoolV i2 -> i1 = i2
  | FloatV i1, FloatV i2 -> i1 = i2
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
  | FPlus, FloatV i1, FloatV i2 -> FloatV (i1 +. i2)
  | FPlus, _, _ -> err ("Both arguments must be integer: +.")
  | FMinus, FloatV i1, FloatV i2 -> FloatV (i1 -. i2)
  | FMinus, _, _ -> err ("Both arguments must be integer: -.")
  | FMult, FloatV i1, FloatV i2 -> FloatV (i1 *. i2)
  | FMult, _, _ -> err ("Both arguments must be integer: *.")
  | FDiv, FloatV i1, FloatV i2 -> FloatV (i1 /. i2)
  | FDiv, _, _ -> err ("Both arguments must be integer: /.")
  | FLt, FloatV i1, FloatV i2 -> BoolV (i1 <. i2)
  | FLt, _, _ -> err ("Both arguments must be integer: <.")

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
    Var (ID (x, _))  -> 
    (try Environment.lookup x env with 
       Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | Var (VARIANT x) -> (try Environment.lookup x env with 
        Environment.Not_bound -> err ("Variable not bound: " ^ x))
  | ILit i -> IntV i
  | BLit b -> BoolV b
  | FLit f -> FloatV f
  | Float_of_int e1 -> 
    let v1 = eval_exp env e1 in
    (match v1 with
     | IntV i -> FloatV (float_of_int i)
     | _ -> err "float_of_int failed"
    )
  | Int_of_float e1 -> 
    let v1 = eval_exp env e1 in
    (match v1 with
     | FloatV f -> IntV (int_of_float f)
     | _ -> err "int_of_float failed"
    )
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
         | ((id, _), e) :: rest ->  
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
          | (top, _) :: [] -> let newenv = Environment.extend top arg !env_ref in
            eval_exp newenv body
          | (top, _) :: rest -> 
            let newenv = Environment.extend top arg !env_ref in
            let dummyenv = ref Environment.empty in
            dummyenv := newenv;
            ListProcV(rest, body, dummyenv)
          | [] -> err("too many arguments"))
       | DProcV(id, body) -> let newenv = Environment.extend id arg env in
         eval_exp newenv body
       | ArityUserV(tyid) ->
         ArityAppUserV (tyid, arg) 
       | e -> err ("Non function value is applied")))
  | DFunExp (id, exp) -> DProcV(id, exp)
  | LetRecExp (id, para, exp1, exp2) ->
    let dummyenv = ref Environment.empty in
    let newenv = Environment.extend id (ProcV(para, exp1, dummyenv)) env in
    dummyenv := newenv;
    eval_exp newenv exp2
  | ListExp exp_list -> 
    ListV (List.map exp_list ~f:(fun e -> eval_exp env e))
  | MatchExp(guard_exp, pattern_list) ->
    let guard_val = eval_exp env guard_exp in
    let rec make_pattern_env pt (ex:dnval) (accum_env: dnval Environment.t) =
      (* recursive function to make env with pattern vars in env *)
      match pt, ex with
      | ConsListPattern (p1, p2), ListV (hdval:: tlval) -> 
        let p1_env = make_pattern_env p1 hdval accum_env in
        make_pattern_env p2 (ListV tlval) p1_env
      | TailListPattern, ListV [] -> accum_env 
      | TuplePattern (p1, p2), TupleV(val1, val2) ->
        let p1_env = make_pattern_env p1 val1 accum_env in
        make_pattern_env p2 val2 p1_env 
      | SingleVariantPattern pt_tyid, UserV v_tyid -> 
        if pt_tyid = v_tyid then accum_env else raise MatchFail
      | VariantPattern (pt_tyid, ipt), ArityAppUserV (v_tyid, varval) -> 
        if pt_tyid = v_tyid then 
          make_pattern_env ipt varval accum_env
        else raise MatchFail
      | RecordPattern (fl, _), RecordV(tyname, content_list) -> 
        List.fold fl ~init:accum_env
          ~f:(fun accum_env (fname, ipt) -> 
              let (_, fval, _) = List.find_exn content_list ~f:(fun (fname_inner, _, _) -> fname = fname_inner) in
              make_pattern_env ipt !fval accum_env)
      | IdPattern id, _ -> 
        if id = "_" then accum_env
        else Environment.extend id ex accum_env
      | UnderbarPattern, _ -> accum_env
      | _, _ -> raise MatchFail
    in
    let rec loop_pattern pl = 
      match pl with
      | (pt, e)::rest -> 
        (try
           let eval_env = make_pattern_env pt guard_val env in
           eval_exp eval_env e
         with MatchFail ->
           loop_pattern rest)
      | [] -> err "match failed" in
    loop_pattern pattern_list
  | TupleExp(e1, e2) -> TupleV(eval_exp env e1, eval_exp env e2)
  | RecordExp (tyname_ref, fieldlist) -> 
    RecordV(!tyname_ref, List.map fieldlist ~f:(fun (fname, fcontent, is_mut_ref) ->
        (fname, ref (eval_exp env fcontent), !is_mut_ref)))
  | RecordAppExp(e1, fieldname) -> 
    let e1val = eval_exp env e1 in
    (match e1val with
     | RecordV(rec_typename, fl) -> 
       let (_, target_val, _) = List.find_exn ~f:(fun (fname_inner, _, _) -> fname_inner = fieldname) fl in
       !target_val
     | _ -> err ("no field with type " ^ fieldname))
  | RecordMuteExp(recordexp, fieldname, newexp) -> 
    let record_v = eval_exp env recordexp in
    let newexp_v = eval_exp env newexp in
    (match record_v with 
     | RecordV(_, fl) -> 
       let (_, content_val_ref, is_mut) = List.find_exn fl 
           ~f:(fun (fname_inner, _, _) -> fname_inner = fieldname) in
       if is_mut then 
         (content_val_ref := newexp_v;
          UnitV)
       else err "field is not mutable"
     | _ -> err "not a record")
  | Reference content -> 
    let content_v = eval_exp env content in
    let new_loc = fresh_location () in
    append_loc new_loc content_v;
    RefV new_loc
  | Assign (i, e1) -> 
    let ref_value = eval_exp env (Var(ID (i, None))) in
    let e1_value = eval_exp env e1 in
    (match ref_value with 
     | RefV loc -> append_loc loc e1_value;
       UnitV
     | _ -> err "cannot assign to non-reference")
  | Deassign e1 -> 
    let e1_val = eval_exp env e1 in
    (match e1_val with
     | RefV loc -> lookup_loc loc
     | _ -> err "could not find reference")
  | Annotated(e, _) -> 
    eval_exp env e

let eval_decl env = function
    Exp e -> let v = eval_exp env e in ("-", env, v)
  | Decl ((id, _), e) -> let v = eval_exp env e in (id, Environment.extend id v env, v)
  | RecDecl(id, para, e) -> (
      let dummyenv = ref Environment.empty in 
      let newenv = Environment.extend id (ProcV(para, e, dummyenv)) env in 
      dummyenv := newenv;
      (id, newenv, ProcV(para, e, dummyenv)))
  | VariantDecl(tyarg_opt, ty_name, variant_list) -> 
    let rec extend_env l accum_env = 
      match l with
      | (h, TyDummy)::t -> 
        let accum_env' = Environment.extend h (UserV h) accum_env in
        extend_env t accum_env'
      | (h, _)::t -> 
        let accum_env' = Environment.extend h (ArityUserV h) accum_env in
        extend_env t accum_env'
      | [] -> accum_env in
    let env' = extend_env variant_list env in
    (* (ty_name, env', ListV (List.map variant_list ~f:(fun (x, _) -> UserV x))) *)
    (ty_name, env', VariantDefV(tyarg_opt, ty_name, variant_list))
  | RecordDecl (tyannot_opt, recname, fieldslist) -> 
    (recname, env, RecordDefV(tyannot_opt, recname, fieldslist))
