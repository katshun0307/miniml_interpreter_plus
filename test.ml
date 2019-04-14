
open Syntax
open Eval
open OUnit
open Core

exception UnexpectedMatch

let semisemi = ";;"

type content = {
  ty: Syntax.ty;
  v:  Eval.dnval;
}

type eval_result = {
  contents: content;
  env: Eval.dnval Environment.t;
  tyenv: Syntax.ty Environment.t;
}

let initial_env = Environment.empty
let initial_tyenv = Environment.empty

let eval env tyenv prog_str = 
  let decl = Parser.toplevel Lexer.main (Lexing.from_string (prog_str ^ semisemi)) in
  let ty, new_tyenv = Typing.ty_decl tyenv decl in
  let (id, newenv, v) = eval_decl env decl in
  {contents = {ty = ty; v = v}; env = newenv; tyenv = new_tyenv}

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
    let rec ty_eqls t1 t2 = 
      match t1, t2 with
      | TyFun (tf11, tf12), TyFun (tf21, tf22) -> (ty_eqls tf11 tf12) && (ty_eqls tf12 tf22)
      | TyList t1, TyList t2 -> ty_eqls t1 t2
      | TyVar _ , TyVar _ -> true
      | TyBool, TyBool -> true
      | TyInt, TyInt -> true
      | _ -> false in
    (ty_eqls c1.ty c2.ty) && c1.v = c2.v in
  let pp_content c = 
    sprintf "{type: %s; value: %s}" (string_of_ty c.ty) (string_of_exval c.v) in
  assert_equal ~cmp:cmp_content ~printer:pp_content

(* test cases *)

let typing_error = Typing.Error("unify: could not resolve type")

let decl_tests = ("test suites for declaration" >::: [
    "single" >:: (fun _ -> assert_equal_content (test_eval_loop ["3"]) ({ty = TyInt; v = IntV 3}));
  ])

let recur_tests = "recursion tests" >::: [
    let prog = "let rec fact = fun n -> if n < 1 then 1 else n * fact (n+ -1) in fact 10" in
    "factorial" >:: (fun _ -> assert_equal_content (test_eval_loop [prog]) {ty = TyInt; v = IntV 3628800});
  ]

let list_tests = "list tests" >::: [
    "simple bool" >:: (fun _ -> assert_equal_content 
                          {ty = TyList TyBool; v = ListV [BoolV true; BoolV false]}
                          (test_eval_loop ["[true; false]"])
                      );
    "simple int" >:: (fun _ -> assert_equal_content 
                         {ty = TyList TyInt; v = ListV [IntV 1; IntV 2]}
                         (test_eval_loop ["[1; 2;]"])
                     );
    "simple empty" >:: (fun _ -> assert_equal_content 
                           {ty = TyList (TyVar 1); v = ListV []}
                           (test_eval_loop ["let x = [] in x"])
                       );
    "assert int" >:: (fun _ -> assert_equal_content
                         {ty = (TyList TyInt); v = ListV[IntV 3; IntV 5]}
                         (test_eval_loop ["let x = 3 in [x; 5]"])
                     );
    "assert int2" >:: (fun _ -> assert_equal_content
                          {ty = TyList TyInt; v = ListV[IntV 3; IntV 3]}
                          (test_eval_loop ["let x = 3 in [x; x]"])
                      );
    "assert int" >:: (fun _ -> assert_equal_content
                         {ty = TyList TyInt; v = ListV[IntV 3; IntV 5]}
                         (test_eval_loop ["let x = 3"; "[x; 5]"])
                     );
    "assert error" >:: (fun _ -> assert_raises
                           typing_error
                           (fun () -> test_eval_loop ["let f x = x in [f 5; f true]"])
                       );
  ]

let match_tests = "match tests" >::: [
    "int match" >:: (fun _ -> assert_equal_content
                        {ty = TyInt; v = IntV 3}
                        (test_eval_loop ["match [3;4;5;6] with | hd::tl -> hd | [] -> 100"])
                    );
    "bool match" >:: (fun _ -> assert_equal_content
                         {ty = TyBool; v = BoolV true}
                         (test_eval_loop ["match [true; false] with | hd::tl -> hd | [] -> false"])
                     );
    "tail match" >:: (fun _ -> assert_equal_content
                         {ty = TyInt; v = IntV 60}
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

let tests = "all tests" >::: [decl_tests; recur_tests; list_tests; match_tests]

let run_test () = 
  run_test_tt_main tests
