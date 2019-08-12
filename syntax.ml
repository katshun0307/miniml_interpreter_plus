open MySet
open Core

exception Error of string

let err s = raise (Error s)

(* ML interpreter / type reconstruction *)

(* ids, used in variable names and user-defined type names *)
type id = string
[@@deriving show]

(* name of variant, starting with capital letters *)
type tyid = string
[@@deriving show]

(* tyvar of zero should not be allocated *)
(* tyvar annotations are negative, tyvars in interpreter are positive *)
type tyvar = int
[@@deriving show]

(* type variable annotations by user *)
(* converted to tyvar uniformly by fresh_tyvar_annot *)
(* ex. 'a *)
type tyvar_annot = string 
[@@deriving show]

type ty = 
  | TyInt 
  | TyBool
  | TyFloat
  | TyUnit
  | TyRef of ty
  | TyVar of tyvar
  | TyFun of ty * ty
  | TyList of ty
  | TyTuple of ty * ty
  | TyUser of id
  | TyParaUser of ty * id 
  | TyDummy (* return type of type declaration *)
[@@deriving show]

type annot_id = string * ty option
[@@deriving show]

type vars = 
  | ID of annot_id 
  | VARIANT of string
[@@deriving show]

type binOp = 
  | Plus 
  | Minus 
  | Mult 
  | Div 
  | Lt 
  | Modulo 
  | Eq 
  | FPlus
  | FMinus
  | FMult 
  | FDiv 
  | FLt
[@@deriving show]

type logicOp = And | Or 
[@@deriving show]

type list_pattern = 
  | Tail 
  | Id of id
  | Cons of id * list_pattern
[@@deriving show]

type match_pattern = 
  | ConsListPattern of match_pattern * match_pattern
  | TailListPattern
  | TuplePattern of match_pattern * match_pattern
  | SingleVariantPattern of tyid 
  | VariantPattern of tyid * match_pattern
  | RecordPattern of (id * match_pattern) list * bool (* when bool is true, there is underbar *)
  | IdPattern of id
  | UnderbarPattern
[@@deriving show]

type exp =
  | Var of vars (* Var "x" --> x *)
  | ILit of int (* ILit 3 --> 3 *)
  | BLit of bool (* BLit true --> true *)
  | FLit of float (* FLit 0.5 --> 0.5 *)
  | Float_of_int of exp
  | Int_of_float of exp
  | ListExp of exp list (* list expression *)
  | BinOp of binOp * exp * exp
  | LogicOp of logicOp * exp * exp
  (* BinOp(Plus, ILit 4, Var "x") --> 4 + x *)
  | IfExp of exp * exp * exp
  (* IfExp(BinOp(Lt, Var "x", ILit 4), 
           ILit 3, 
           Var "x") --> 
     if x<4 then 3 else x *)
  | MultiLetExp of (annot_id * exp) list * exp
  | FunExp of annot_id list * exp (* static function expression *)
  | DFunExp of id * exp (* dynamic function expression *)
  | AppExp of exp * exp (* function application expression *)
  | LetRecExp of id * id * exp * exp (* recursive function expression *)
  | MatchExp of exp * (match_pattern * exp) list (* list match *)
  | TupleExp of exp * exp (* tuple expression *)
  | RecordExp of id ref * (id * exp * bool ref) list (* id option (typename) is none by default. *)
  | RecordAppExp of exp * id (* exp of record and id of fieldname *)
  | RecordMuteExp of exp * id * exp (* exp of record and id of fieldname *)
  | Reference of exp
  | Assign of id * exp
  | Deassign of exp
  | Annotated of exp * ty
[@@deriving show]

type program =
  | Exp of exp
  | Decl of annot_id * exp
  | RecDecl of id * id * exp
  | VariantDecl of string option * id * ((tyid * ty) list)
  | RecordDecl of string option * id * ((id * ty * bool) list)
[@@deriving show]

(* type scheme *)
type tysc = TyScheme of tyvar list * ty
[@@deriving show]

let tysc_of_ty t = TyScheme([], t)

let ty_of_tysc (TyScheme(_, ty)) = ty

let tyvar_string_of_int n =
  let inner n = 
    (* 26 * block + offset *)
    let start_code = Char.to_int 'a' in
    let alphabet_of_int n = 
      (if n <= 26 then
         Char.escaped (Char.of_int_exn (n + start_code))
       else err "unexpected input") in
    let offset = n mod 26 in
    let block = (n - offset) / 26 in
    if block = 0 then "'" ^ alphabet_of_int offset
    else "'" ^ alphabet_of_int offset ^ string_of_int block in
  if n >= 0 then inner n else "_" ^ inner (-n)

(* optional argument tyvar_str: convert tyvars to specific string *)
let rec string_of_ty ?tyvar_str:(tyvar_str=[]) = function
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFloat -> "float"
  | TyUnit -> "unit"
  | TyVar id -> 
    (match List.Assoc.find tyvar_str ~equal:(=) id with
     | Some x -> x
     | None -> tyvar_string_of_int id)
  | TyFun(a, b) -> 
    (match a with
     | TyFun (_, _) -> "(" ^ string_of_ty ~tyvar_str a ^ ") -> " ^ string_of_ty ~tyvar_str b
     | _ ->  string_of_ty ~tyvar_str a ^ " -> " ^ string_of_ty ~tyvar_str b )
  | TyList t -> (string_of_ty t) ^ " list"
  | TyTuple (t1, t2) -> "(" ^ string_of_ty ~tyvar_str t1 ^ ", " ^ string_of_ty ~tyvar_str t2 ^ ")"
  | TyUser id -> id
  | TyParaUser(t, id) -> string_of_ty ~tyvar_str t ^ " " ^ id
  | TyRef t1 -> string_of_ty ~tyvar_str t1 ^ " ref"
  | TyDummy -> "TyDummy"

let string_of_eqls eqls =
  let open Core in
  let string_of_eql (t1, t2) =
    Printf.sprintf "(%s, %s)" (string_of_ty t1) (string_of_ty t2) in
  "[" ^ String.concat ~sep:"; " (List.map eqls ~f:string_of_eql) ^ "]\n"

let rec string_of_pattern p = 
  let open Core in
  match p with
  | ConsListPattern (p1, p2) -> 
    sprintf "%s :: %s" (string_of_pattern p1) (string_of_pattern p2)
  | TailListPattern -> "[]"
  | TuplePattern (p1, p2) -> 
    sprintf "(%s, %s)" (string_of_pattern p1) (string_of_pattern p2)
  | SingleVariantPattern tyid -> "Variant(" ^ tyid ^ ")"
  | VariantPattern (tyid, pin) -> 
    sprintf "%s(%s)" tyid (string_of_pattern pin)
  | RecordPattern (l, _) -> 
    "{" ^ String.concat ~sep:"; " 
      (List.map l ~f:(fun (fname, p) -> sprintf "%s = %s" fname (string_of_pattern p)))  ^ "}"
  | IdPattern i -> i
  | UnderbarPattern -> "__"

let rec string_of_list_pattern (lp: list_pattern) = 
  match lp with
  | Cons(hd, tl) -> hd ^ "::" ^ string_of_list_pattern tl
  | Id i -> i
  | Tail -> "[]" 

let string_of_tysc = function
  | TyScheme(bl, ty) -> 
    let bound_vars = "[" ^ Core.String.concat ~sep:"," (List.map ~f:(fun b -> tyvar_string_of_int b) bl) ^ "]" in
    bound_vars ^ string_of_ty ty

let renumber_ty t = 
  let numref = ref 0 in 
  let fresh_num () = 
    let n = !numref in
    numref := n + 1;
    n in
  let renumber_tyvar tv assoc = 
    let open Core in
    match List.Assoc.find assoc ~equal:(=) tv with
    | Some x -> (x, assoc)
    | None -> let new_tyvar = fresh_num () in
      (new_tyvar, List.Assoc.add assoc ~equal:(=) tv new_tyvar) in
  let rec loop ty assoc = 
    match ty with
    | TyFun(t1, t2) -> 
      let t1', assoc1 = loop t1 assoc in
      let t2', assoc2 = loop t2 (assoc1 @ assoc) in
      (TyFun(t1', t2'), assoc1 @ assoc2)
    | TyTuple(t1, t2) -> 
      let t1', assoc1 = loop t1 assoc in
      let t2', assoc2 = loop t2 (assoc1 @ assoc) in
      (TyTuple(t1', t2'), assoc1 @ assoc2)
    | TyList t1 -> 
      let t', assoc' = loop t1 assoc in
      (TyList t', assoc')
    | TyRef t1 -> 
      let t', assoc' = loop t1 assoc in
      (TyRef t', assoc')
    | TyParaUser(t1, i) -> 
      let t', assoc' = loop t1 assoc in
      (TyParaUser (t', i), assoc')
    | TyVar tv1 -> 
      let tv', assoc' =  renumber_tyvar tv1 assoc in
      (TyVar tv', assoc')
    | TyInt | TyBool | TyFloat | TyUnit | TyDummy | (TyUser _) as tt ->
      (tt, assoc) in
  (* | _ as tt -> (tt, assoc) in *)
  let (res, _) = loop t [] in res

(* returns new type variables with fresh_tyvar() *)
let fresh_tyvar = 
  let counter = ref 1 in
  let body () =
    let v = !counter in
    counter := v + 1; v
  in body

(* returns tyvar for type annotation *)
let fresh_tyvar_annot = 
  let counter = ref (-1) in
  let assoc = ref [] in
  let body (s: string) = 
    match List.Assoc.find !assoc ~equal:(=) s with
    | Some x -> x
    | None -> 
      let v = !counter in
      counter := v + 1;
      assoc := (s, v)::!assoc; v
  in body

(* 与えられた型中の型変数の集合を返す関数 *)
let freevar_ty ty_in = 
  let rec loop ty current = 
    (match ty with
     | TyVar a -> MySet.insert a current
     | TyFun(a, b) -> MySet.union (loop a current) (loop b current)
     | _ -> current) in
  loop ty_in MySet.empty

(* 与えられた型スキーム中の自由変数の集合を返す関数 *)
let freevar_tysc (TyScheme(b, ty)) = 
  let bounds = MySet.from_list b in
  let rec loop ty = 
    match ty with
    | TyInt | TyBool | TyFloat | TyUser _ | TyDummy | TyUnit -> MySet.empty
    | TyFun (t1, t2) -> MySet.union (loop t1) (loop t2)
    | TyList t1 | TyRef t1 | TyParaUser(t1, _) -> loop t1
    | TyVar v -> 
      if MySet.member v bounds
      then MySet.empty
      else MySet.singleton v
    | TyTuple (t1, t2) ->
      MySet.union (loop t1) (loop t2)
  in let freevar_set = loop ty in
  MySet.to_list freevar_set

let id_of_annot_id (ian: annot_id): id = 
  match ian with
  | (i, _) -> i
