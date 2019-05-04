open Syntax
open Eval
open OUnit
open Core

exception UnexpectedMatch

let semisemi = ";;"

type content = {
  ty: Syntax.ty;
  v: Eval.dnval option;
}

type eval_result = {
  contents: content;
  env: Eval.dnval Environment.t;
  tyenv: Syntax.tysc Environment.t;
}

let initial_env = Environment.empty
let initial_tyenv = Environment.empty

let eval env tyenv prog_str = 
  let decl = Parser.toplevel Lexer.main (Lexing.from_string (prog_str ^ semisemi)) in
  let tysc, new_tyenv = Typing.ty_decl tyenv decl in
  let (id, newenv, v) = eval_decl env decl in
  {contents = {ty = ty_of_tysc tysc; v = Some v}; env = newenv; tyenv = new_tyenv}

let rec eval_loop env tyenv prog_lst = 
  match prog_lst with
  | hd:: [] -> 
    (eval env tyenv hd).contents
  | hd:: tl -> 
    let res = eval env tyenv hd in
    eval_loop res.env res.tyenv tl
  | [] -> raise UnexpectedMatch

let test_eval_loop prog_lst =
  eval_loop initial_env initial_tyenv prog_lst 

let assert_equal_content = 
  let cmp_content c1 c2 = 
    let rec ty_eqls t1 t2 ty_assoc = 
      match t1, t2 with
      | TyFun (tf11, tf12), TyFun (tf21, tf22) -> 
        let ty_eql1, ty_assoc1 = ty_eqls tf11 tf12 ty_assoc in
        let ty_eql2, ty_assoc2 = ty_eqls tf12 tf22 ty_assoc in
        (ty_eql1 && ty_eql2, ty_assoc1 @ ty_assoc2)
      | TyList t1, TyList t2 -> ty_eqls t1 t2 ty_assoc
      | TyVar tv1 , TyVar tv2 -> 
        (match Core.List.Assoc.find ty_assoc ~equal:(=) tv1 with
         | Some tv2_expect -> (tv2 = tv2_expect, ty_assoc)
         | None ->  (true, Core.List.Assoc.add ty_assoc ~equal:(=) tv1 tv2))
      | TyBool, TyBool -> (true, ty_assoc)
      | TyInt, TyInt -> (true, ty_assoc)
      | _ -> (false, ty_assoc) in
    let v_eqls v1o v2o = 
      match v1o, v2o with
      | Some v1, Some v2 -> v1 = v2
      | Some v1, None | None, Some v1 -> true
      | _ -> true in
    let ty_is_equal, _ = ty_eqls c1.ty c2.ty [] in
    ty_is_equal && v_eqls c1.v c2.v in
  let pp_content c = 
    let val_str = 
      match c.v with
      | Some v -> string_of_exval v
      | None -> "undefined" in
    sprintf "{type: %s; value: %s}" (string_of_ty c.ty) val_str in
  assert_equal ~cmp:cmp_content ~printer:pp_content

(* test cases *)

let typing_error = Typing.Error("unify: could not resolve type")

let decl_tests = ("test suites for declaration" >::: [
    "single" >:: (fun _ -> assert_equal_content (test_eval_loop ["3"]) ({ty = TyInt; v = Some (IntV 3)}));
  ])

let recur_tests = "recursion tests" >::: [
    let prog = "let rec fact = fun n -> if n < 1 then 1 else n * fact (n+ -1) in fact 10" in
    "factorial" >:: (fun _ -> assert_equal_content (test_eval_loop [prog]) {ty = TyInt; v = Some (IntV 3628800)});
  ]

let list_tests = "list tests" >::: [
    "simple bool" >:: (fun _ -> assert_equal_content 
                          {ty = TyList TyBool; v = Some (ListV [BoolV true; BoolV false])}
                          (test_eval_loop ["[true; false]"])
                      );
    "simple int" >:: (fun _ -> assert_equal_content 
                         {ty = TyList TyInt; v = Some (ListV [IntV 1; IntV 2])}
                         (test_eval_loop ["[1; 2;]"])
                     );
    "simple empty" >:: (fun _ -> assert_equal_content 
                           {ty = TyList (TyVar 1); v = Some (ListV [])}
                           (test_eval_loop ["let x = [] in x"])
                       );
    "assert int" >:: (fun _ -> assert_equal_content
                         {ty = (TyList TyInt); v = Some (ListV[IntV 3; IntV 5])}
                         (test_eval_loop ["let x = 3 in [x; 5]"])
                     );
    "assert int2" >:: (fun _ -> assert_equal_content
                          {ty = TyList TyInt; v = Some (ListV[IntV 3; IntV 3])}
                          (test_eval_loop ["let x = 3 in [x; x]"])
                      );
    "assert int" >:: (fun _ -> assert_equal_content
                         {ty = TyList TyInt; v = Some (ListV[IntV 3; IntV 5])}
                         (test_eval_loop ["let x = 3"; "[x; 5]"])
                     );
    "assert error" >:: (fun _ -> assert_raises
                           typing_error
                           (fun () -> test_eval_loop ["let f x = x in [f 5; f true]"])
                       );
  ]

let match_tests = "match tests" >::: [
    "int match" >:: (fun _ -> assert_equal_content
                        {ty = TyInt; v = Some (IntV 3)}
                        (test_eval_loop ["match [3;4;5;6] with | hd::tl -> hd | [] -> 100"])
                    );
    "bool match" >:: (fun _ -> assert_equal_content
                         {ty = TyBool; v = Some (BoolV true)}
                         (test_eval_loop ["match [true; false] with | hd::tl -> hd | [] -> false"])
                     );
    "tail match" >:: (fun _ -> assert_equal_content
                         {ty = TyInt; v = Some (IntV 60)}
                         (test_eval_loop ["let x = [] in match x with | h::t -> 30 | [] -> 60;;"])
                     );
    "int match failure" >:: (fun _ -> assert_raises
                                typing_error
                                (fun _ -> test_eval_loop ["match [3;4;5;6] with | hd::tl -> tl | [] -> 100"])
                            );
    "int var same failure" >:: (fun _ -> assert_raises
                                   (Eval.Error("match variable must not be same"))
                                   (fun _ -> test_eval_loop ["match [3;4;5;6] with | hd::hd -> hd | [] -> 100"])
                               );
  ]

let polylet_tests = "polylet tests" >::: [
    "1" >:: (fun _ -> assert_raises
                typing_error
                (fun _ -> test_eval_loop ["let rec f = fun x -> f in f"])
            );
    "2" >:: (fun _ -> assert_equal_content
                {ty = TyFun(TyVar 1, TyVar 2); v = None}
                (test_eval_loop ["let rec f = fun x -> f x in f"])
            );
    "3" >:: (fun _ -> assert_equal_content
                {ty = TyFun(TyVar 1, TyVar 1); v = None}
                (test_eval_loop ["let rec f = fun x -> f (f x) in f	"])
            );
    "4" >:: (fun _ -> assert_equal_content
                {ty = TyFun(TyFun(TyFun(TyVar 1, TyVar 2), TyFun(TyVar 1, TyVar 2)), TyFun(TyVar 1, TyVar 2)); v = None}
                (test_eval_loop ["let rec fix_fun = fun g -> fun x -> g (fix_fun g) x in fix_fun"])
            );
    "5" >:: (fun _ -> assert_equal_content
                {ty = TyFun(TyFun(TyVar 1, TyVar 1), TyVar 1); v = None}
                (test_eval_loop ["fun f -> let rec x = fun z -> f (x z) in x 666"])
            );
    "6" >:: (fun _ -> assert_equal_content
                {ty = TyFun(TyInt, TyFun(TyVar 1, TyVar 1)); v = None}
                (test_eval_loop ["let rec f = fun x -> fun y -> if x < 0 then y else f (x + -1) y in f"])
            );
  ]

let tests = "all tests" >::: [
    decl_tests; 
    recur_tests; 
    list_tests; 
    match_tests;
    (* polylet_tests; *)
  ]

let run_test () = 
  print_string "running tests...\n";
  run_test_tt_main tests
