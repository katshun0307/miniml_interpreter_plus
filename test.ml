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

let test_eval_loop =
  eval_loop initial_env initial_tyenv  

let assert_equal_content = 
  let cmp_content c1 c2 = 
    let v_eqls v1o v2o = 
      match v1o, v2o with
      | Some v1, Some v2 -> v1 = v2
      | Some v1, None | None, Some v1 -> true
      | _ -> true in
    let renum_t1 = Syntax.renumber_ty c1.ty in
    let renum_t2 = Syntax.renumber_ty c2.ty in
    let ty_is_equal = (renum_t1 = renum_t2) in
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
let match_exhaustive_error = Typing.MatchNotExhaustive

let binop_tests = "binary operation tests" >::: [
    "simple +" >:: (fun _ -> assert_equal_content 
                       {ty = TyInt; v = Some (IntV 5)}
                       (test_eval_loop ["3 + 2"])
                   );
    "simple -" >:: (fun _ -> assert_equal_content 
                       {ty = TyInt; v = Some (IntV 1)}
                       (test_eval_loop ["3 - 2"])
                   );
    "simple *" >:: (fun _ -> assert_equal_content 
                       {ty = TyInt; v = Some (IntV 6)}
                       (test_eval_loop ["3 * 2"])
                   );
    "simple /" >:: (fun _ -> assert_equal_content 
                       {ty = TyInt; v = Some (IntV 2)}
                       (test_eval_loop ["5 / 2"])
                   );
    "simple mod" >:: (fun _ -> assert_equal_content 
                         {ty = TyInt; v = Some (IntV 1)}
                         (test_eval_loop ["3 % 2"])
                     );
    "priority test1" >:: (fun _ -> assert_equal_content 
                             {ty = TyInt; v = Some (IntV 13)}
                             (test_eval_loop ["3 + 2 * 5"])
                         );
    "priority test2" >:: (fun _ -> assert_equal_content 
                             {ty = TyBool; v = Some (BoolV true)}
                             (test_eval_loop ["3 - 2 * 5 < 2 + 3 - 3 * 5 / 2"])
                         );
    "priority test3" >:: (fun _ -> assert_equal_content 
                             {ty = TyInt; v = Some (IntV 4)}
                             (test_eval_loop ["3 + 3 * 3 % 2"])
                         );
    "priority test4" >:: (fun _ -> assert_equal_content 
                             {ty = TyInt; v = Some (IntV 0)}
                             (test_eval_loop ["3 + 3 * 2 / 5 % 3 - 4;;"])
                         );
    "priority test5" >:: (fun _ -> assert_equal_content 
                             {ty = TyInt; v = Some (IntV 0)}
                             (test_eval_loop ["3 % 4 * 7 % 2 / 4;;"])
                         );
    "priority test6" >:: (fun _ -> assert_equal_content 
                             {ty = TyInt; v = Some (IntV 0)}
                             (test_eval_loop ["3 / 4 * 3 % 2 / 5 % 3 * 3;;"])
                         );
  ]

let float_binop_tests = "float binary operation tests" >::: [
    "test0" >:: (fun _ -> assert_equal_content 
                    {ty = TyBool; v = Some (BoolV false)}
                    (test_eval_loop ["0.5 <. 0.2"])
                );
    "test1" >:: (fun _ -> assert_equal_content 
                    {ty = TyBool; v = Some (BoolV false)}
                    (test_eval_loop ["2. = 5."])
                );
    "test2" >:: (fun _ -> assert_equal_content 
                    {ty = TyBool; v = Some (BoolV true)}
                    (test_eval_loop ["2. = 2."])
                );
    "test3" >:: (fun _ -> assert_equal_content 
                    {ty = TyBool; v = Some (BoolV true)}
                    (test_eval_loop ["2. <. 5. && 3. <. 8.;"])
                );
    "test4" >:: (fun _ -> assert_equal_content 
                    {ty = TyBool; v = Some (BoolV false)}
                    (test_eval_loop ["0.5 <. 0.2 || 5 < 3 || false"])
                );
  ]

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
    "tuple match tail cons" >:: (fun _ -> assert_equal_content
                                    {ty = TyInt; v = Some (IntV 1)}
                                    (test_eval_loop ["let x = [] in let y = [1;2;3] in match (x, y) with | h::t, a::b -> 30 | [], h::t -> h | h::t, [] -> 40 | [], [] -> 5;;"])
                                );
    "tuple match cons cons" >:: (fun _ -> assert_equal_content
                                    {ty = TyInt; v = Some (IntV 4)}
                                    (test_eval_loop ["let x = [4;5;6] in let y = [1;2;3] in match (x, y) with | h::t, a::b -> h | h::t, [] -> 500 | [], h::t -> h | [], [] -> 100;;"])
                                );
    "tuple match second" >:: (fun _ -> assert_equal_content
                                 {ty = TyInt; v = Some (IntV 5)}
                                 (test_eval_loop ["let x = [4;5;6] in let y = [1;2;3] in match (x, y) with | h::h2::t, a::b -> h2 | [], h::t -> h | h1, a -> 40;;"])
                             );
    "tuple match without paren" >:: (fun _ -> assert_equal_content
                                        {ty = TyInt; v = Some (IntV 5)}
                                        (test_eval_loop ["let x = [4;5;6] in let y = [1;2;3] in match x, y with | h::h2::t, a::b -> h2 | [], h::t -> h | h1, a -> 500;;"])
                                    );
    "int match failure" >:: (fun _ -> assert_raises
                                typing_error
                                (fun _ -> test_eval_loop ["match [3;4;5;6] with | hd::tl -> tl | [] -> 100"])
                            );
    "match not exhaustive1" >:: (fun _ -> assert_raises
                                    match_exhaustive_error
                                    (fun _ -> test_eval_loop ["match [3;4;5;6] with | hd::tl -> tl"])
                                );    
    "match not exhaustive2" >:: (fun _ -> assert_raises
                                    match_exhaustive_error
                                    (fun _ -> test_eval_loop ["match [3;4;5;6] with | hd::hd2::tl -> tl | [] -> 100"])
                                );    
    "tuple match not exhaustive1" >:: (fun _ -> assert_raises
                                          match_exhaustive_error
                                          (fun _ -> test_eval_loop ["match [3;4;5;6], [1;2;3] with | hd::tl, ho -> tl"])
                                      );    
    "tuple match not exhaustive2" >:: (fun _ -> assert_raises
                                          match_exhaustive_error
                                          (fun _ -> test_eval_loop ["match [3;4;5;6], [1;2;3] with | hd::hd2::tl, hh1::hh2::tt2 -> tl | [], []  -> 100"])
                                      );    
    "int var same failure" >:: (fun _ -> assert_raises
                                   (Typing.Error("match variable must not be same"))
                                   (fun _ -> test_eval_loop ["match [3;4;5;6] with | hd::hd -> hd | [] -> 100"])
                               );
  ]

let advanced_match_tests = "advanced match" >::: [
    "user no arity match" >:: (fun _ -> assert_equal_content
                                  {ty = TyInt; v = Some (IntV 3)}
                                  (test_eval_loop ["type food = Yogurt | Hotdog"; "match Hotdog with | Hotdog -> 3 | Yogurt -> 5"])
                              );
    "tuple match not exhaustive2" >:: (fun _ -> assert_raises
                                          match_exhaustive_error
                                          (fun _ -> test_eval_loop ["type food = Yogurt | Hotdog"; "match Hotdog with | Hotdog -> 3"])
                                      );
    "user arity match" >:: (fun _ -> assert_equal_content
                               {ty = TyInt; v = Some (IntV 3)}
                               (test_eval_loop ["type food = Yogurt of int | Hotdog of int"; "match Hotdog 3 with | Hotdog a -> a | Yogurt b -> b"])
                           );
    "user arity match 2" >:: (fun _ -> assert_equal_content
                                 {ty = TyInt; v = Some (IntV 3)}
                                 (test_eval_loop ["type food = Yogurt of int | Hotdog of bool"; "match Hotdog true with | Hotdog b -> 3 | Yogurt b -> b"])
                             );
    "user arity match not exhaustive2" >:: (fun _ -> assert_raises
                                               match_exhaustive_error
                                               (fun _ -> test_eval_loop ["type food = Yogurt of int | Hotdog of bool"; "match Hotdog true with Hotdog b -> 3"])
                                           );
    (* ub stands for underbar *)
    "user arity match with ub" >:: (fun _ -> assert_equal_content
                                       {ty = TyInt; v = Some (IntV 3)}
                                       (test_eval_loop ["type food = Yogurt of int | Hotdog of int"; "match Hotdog 3 with | Hotdog _ -> 3 | Yogurt _ -> 5"])
                                   );
    "user arity match 2 with ub" >:: (fun _ -> assert_equal_content
                                         {ty = TyInt; v = Some (IntV 3)}
                                         (test_eval_loop ["type food = Yogurt of int | Hotdog of bool"; "match Hotdog true with | Hotdog _ -> 3 | Yogurt _ -> 10"])
                                     );
    "user arity match not exhaustive2 with ub" >:: (fun _ -> assert_raises
                                                       match_exhaustive_error
                                                       (fun _ -> test_eval_loop ["type food = Yogurt of int | Hotdog of bool"; "match Hotdog true with Hotdog _ -> 3"])
                                                   );
    "user complex arity match " >:: (fun _ -> assert_equal_content
                                        {ty = TyInt; v = Some (IntV 8)}
                                        (test_eval_loop ["type food = Yogurt of int * int | Hotdog of int * int";
                                                         "match Hotdog (3, 5) with | Hotdog (a, b) -> a + b | Yogurt(a, b) -> a;;"])
                                    );
  ]

let advanced_tests = "advanced code tests" >::: [
    "eval type simple test" >:: (fun _ -> assert_equal_content
                                    {ty = TyInt; v = Some (IntV 3)}
                                    (test_eval_loop ["type tree = Sum | Mult"
                                                    ;"let a = Sum"
                                                    ;"let eval x = match x with
                                              | Sum -> 3
                                              | Mult -> 5"
                                                    ;"eval a"])
                                );
    "eval type test" >:: (fun _ -> assert_equal_content
                             {ty = TyInt; v = Some (IntV 55)}
                             (test_eval_loop ["type tree = Sum of int * int | Mult of int * int";
                                              "let a = Sum (5, 50)";
                                              "let eval x = match x with
                                              | Sum (a, b) -> a + b
                                              | Mult (a, b) -> a * b";
                                              "eval a"])
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

let user_type_tests = "user type tests" >::: [
    "basic single" >:: (fun _ -> assert_equal_content
                           {ty = TyUser "food"; v = None}
                           (test_eval_loop ["type food = Yogurt"; "Yogurt"])
                       );
    "basic multiple" >:: (fun _ -> assert_equal_content
                             {ty = TyUser "food"; v = None}
                             (test_eval_loop ["type food = Yogurt | Hotdog"; "Hotdog"])
                         );
    "basic single ty" >:: (fun _ -> assert_equal_content
                              {ty = TyUser "food"; v = Some (ArityAppUserV("Yogurt", (IntV 5)))}
                              (test_eval_loop ["type food = Yogurt of int"; "Yogurt 5"])
                          );
    "basic multiple ty" >:: (fun _ -> assert_equal_content
                                {ty = TyUser "food"; v = Some (ArityAppUserV("Hotdog", (IntV 3)))}
                                (test_eval_loop ["type food = Yogurt of int | Hotdog of int"; "Hotdog 3"])
                            );
  ]

let record_tests = "record tests" >::: [
    "basic decl0" >:: (fun _ -> assert_equal_content
                          {ty = TyUser "person"; v = None}
                          (test_eval_loop ["type person = { age: int; alive: bool}"; 
                                           "let a = { age = 40; alive = true}";
                                           "a"])
                      );
    "basic decl1" >:: (fun _ -> assert_equal_content
                          {ty = TyBool; v = Some (BoolV true)}
                          (test_eval_loop ["type person = { age: int; alive: bool}"; 
                                           "let a = { age = 40; alive = true}";
                                           "a.alive"])
                      );
    "basic decl2" >:: (fun _ -> assert_equal_content
                          {ty = TyInt; v = Some (IntV 40)}
                          (test_eval_loop ["type person = { age: int; alive: bool}"; 
                                           "let a = { age = 40; alive = true}";
                                           "a.age"])
                      );
    "record match0" >:: (fun _ -> assert_equal_content
                            {ty = TyFun(TyUser "person", TyInt); v = None}
                            (test_eval_loop ["type person = { age: int; alive: bool}"; 
                                             "let f x = match x with | {age = a; alive = b} -> a"])
                        );
    "record match1" >:: (fun _ -> assert_equal_content
                            {ty = TyInt; v = Some (IntV 40)}
                            (test_eval_loop ["type person = { age: int; alive: bool}"; 
                                             "let f x = match x with | {age = a; alive = b} -> a";
                                             "let a = { age = 40; alive = true}";
                                             "f a"])
                        );
    "record match exhaustivity error0" >:: (fun _ -> assert_raises
                                               match_exhaustive_error
                                               (fun _ -> test_eval_loop ["type person = { age: int; alive: bool}";
                                                                         "let x = {age = 3; alive = false}";
                                                                         "match x with | {age = a;} -> a"])
                                           );
    "record match exhaustivity error1" >:: (fun _ -> assert_raises
                                               match_exhaustive_error
                                               (fun _ -> test_eval_loop ["type person = { age: int list; alive: bool}";
                                                                         "let x = {age = [4;5]; alive = true}";
                                                                         "match x with | {age = a :: c :: []; alive = b} -> 3 | {age = []; alive = b } -> 50"])
                                           );
  ]

let ref_tests = "ref tests" >::: [
    "basic ref0" >:: (fun _ -> assert_equal_content
                         {ty = TyRef TyInt; v = None}
                         (test_eval_loop ["let a = ref 4"; "a"])
                     );
    "basic ref1" >:: (fun _ -> assert_equal_content
                         {ty = TyInt; v = Some(IntV 3)}
                         (test_eval_loop ["let a = ref 3"; "!a"])
                     );
    "basic ref2" >:: (fun _ -> assert_equal_content
                         {ty =TyInt; v = Some(IntV 100)}
                         (test_eval_loop ["let a = ref 4"; "a := 100"; "!a"])
                     );
    "advanced ref0" >:: (fun _ -> assert_equal_content
                            {ty = TyInt; v = Some(IntV 100)}
                            (test_eval_loop ["let a = ref 3"; "let b = a"; "a:=100"; "!a"])
                        );
    "advanced ref1" >:: (fun _ -> assert_equal_content
                            {ty = TyInt; v = Some(IntV 100)}
                            (test_eval_loop ["let a = ref 3"; "let b = a"; "a:=100"; "!b"])
                        );
    "advanced ref2" >:: (fun _ -> assert_equal_content
                            {ty = TyInt; v = Some(IntV 100)}
                            (test_eval_loop ["let a = ref 3"; "let b = a"; "b:=100"; "!a"])
                        );
    "advanced ref3" >:: (fun _ -> assert_equal_content
                            {ty = TyInt; v = Some(IntV 100)}
                            (test_eval_loop ["let a = ref 3"; "let b = a"; "b:=100"; "!b"])
                        );
  ]

let tests = "all tests" >::: [
    binop_tests;
    float_binop_tests;
    decl_tests; 
    recur_tests; 
    list_tests; 
    match_tests;
    polylet_tests;
    user_type_tests;
    record_tests;
    advanced_match_tests;
    advanced_tests;
    ref_tests;
  ]

let run_test () = 
  print_string "running tests...\n";
  run_test_tt_main tests
