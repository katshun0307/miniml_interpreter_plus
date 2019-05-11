open MySet

exception Error of string

let err s = raise (Error s)

(* ML interpreter / type reconstruction *)
type id = string
type tyid = string

type binOp = Plus | Minus | Mult | Div | Lt | Modulo | Eq
type logicOp = And | Or 

type list_pattern = 
  | Tail 
  | Id of id
  | Cons of id * list_pattern

type tuple_pattern = 
  list_pattern * list_pattern

type match_pattern = 
  | ListPattern of list_pattern 
  | TuplePattern of tuple_pattern

type tyvar = int

type ty = 
  | TyInt 
  | TyBool
  | TyVar of tyvar
  | TyFun of ty * ty
  | TyList of ty
  | TyTuple of ty * ty
  | TyUser of id (* user defined type *)
  | TyDummy (* return type of type declaration *)

type exp =
  | Var of id (* Var "x" --> x *)
  | ILit of int (* ILit 3 --> 3 *)
  | BLit of bool (* BLit true --> true *)
  | ListExp of exp list (* list expression *)
  | BinOp of binOp * exp * exp
  | LogicOp of logicOp * exp * exp
  (* BinOp(Plus, ILit 4, Var "x") --> 4 + x *)
  | IfExp of exp * exp * exp
  (* IfExp(BinOp(Lt, Var "x", ILit 4), 
           ILit 3, 
           Var "x") --> 
     if x<4 then 3 else x *)
  | MultiLetExp of (id * exp) list * exp
  | FunExp of id list * exp (* static function expression *)
  | DFunExp of id * exp (* dynamic function expression *)
  | AppExp of exp * exp (* function application expression *)
  | LetRecExp of id * id * exp * exp (* recursive function expression *)
  | MatchExp of exp * (match_pattern * exp) list (* list match *)
  | TupleExp of exp * exp (* tuple expression *)
  | UserExp of tyid (* instance of user-defined type *)

type program =
    Exp of exp
  | Decl of id * exp
  | RecDecl of id * id * exp
  | TypeDecl of id * (tyid list)

(* type scheme *)
type tysc = TyScheme of tyvar list * ty

let tysc_of_ty t = TyScheme([], t)

let ty_of_tysc (TyScheme(_, ty)) = ty

let tyvar_string_of_int n =
  (* 26 * block + offset *)
  let start_code = Char.code 'a' in
  let alphabet_of_int n = 
    (if n <= 26 then
       Char.escaped (Char.chr (n + start_code))
     else err "unexpected input") in
  let offset = n mod 26 in
  let block = (n - offset) / 26 in
  if block = 0 then "'" ^ alphabet_of_int offset
  else "'" ^ alphabet_of_int offset ^ string_of_int block

let rec pp_ty = function
  | TyInt -> print_string "int"
  | TyBool -> print_string "bool"
  | TyVar id -> print_string (tyvar_string_of_int id)
  | TyFun(a, b)-> 
    print_string "(";
    (pp_ty a;
     print_string " -> ";
     pp_ty b;)
  | TyList t -> 
    pp_ty t;
    print_string " list"
  | TyTuple (t1, t2) -> 
    (print_string "(";
     pp_ty t1;
     print_string ", ";
     pp_ty t2;
     print_string ")")
  | TyUser id -> print_string id
  | TyDummy -> print_string "@@@"

let rec string_of_ty = function
  | TyInt ->  "int"
  | TyBool ->  "bool"
  | TyVar id ->  tyvar_string_of_int id
  | TyFun(a, b) -> 
    (match a with
     | TyFun (_, _) -> "(" ^ string_of_ty a ^ ") -> " ^ string_of_ty b
     | _ ->  string_of_ty a ^ " -> " ^ string_of_ty b )
  | TyList t -> (string_of_ty t) ^ " list"
  | TyTuple (t1, t2) -> "(" ^ string_of_ty t1 ^ ", " ^ string_of_ty t2 ^ ")"
  | TyUser id -> id
  | TyDummy -> "@@@"

let rec string_of_list_pattern (lp: list_pattern) = 
  match lp with
  | Cons(hd, tl) -> hd ^ "::" ^ string_of_list_pattern tl
  | Id i -> i
  | Tail -> "[]" 

let string_of_tysc = function
  | TyScheme(bl, ty) -> 
    let bound_vars = "[" ^ Core.String.concat ~sep:"," (List.map (fun b -> tyvar_string_of_int b) bl) ^ "]" in
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
    | TyList t1 -> loop t1 assoc
    | TyVar tv1 -> 
      let tv', assoc' =  renumber_tyvar tv1 assoc in
      (TyVar tv', assoc')
    | _ as tt -> (tt, assoc) in
  let (res, _) = loop t [] in res

(* returns new type variables with fresh_tyvar() *)
let fresh_tyvar = 
  let counter = ref 0 in
  let body () =
    let v = !counter in
    counter := v + 1; v
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
    | TyInt | TyBool | TyUser _ | TyDummy -> MySet.empty
    | TyFun (t1, t2) -> MySet.union (loop t1) (loop t2)
    | TyList t1 -> loop t1
    | TyVar v -> 
      if MySet.member v bounds
      then MySet.empty
      else MySet.singleton v
    | TyTuple (t1, t2) ->
      MySet.union (loop t1) (loop t2)
  in let freevar_set = loop ty in
  MySet.to_list freevar_set
