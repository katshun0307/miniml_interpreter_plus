open Syntax
open Eval
open Typing

let test = ref false

let rec read_eval_print env tyenv =
  print_string "# ";
  flush stdout;
  try
    let decl = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
    let ty, new_tyenv = ty_decl tyenv decl in
    let (id, newenv, v) = eval_decl env decl in
    Printf.printf "val %s : " id;
    print_string (string_of_ty ty);
    print_string " = ";
    pp_val v;
    print_newline();
    read_eval_print newenv new_tyenv
  with e ->
    let msg = Printexc.to_string e in
    print_string ("there was an error: " ^ msg ^ "\n");
    read_eval_print env tyenv;;

type eval_result = {
  ty: Syntax.ty;
  v:  Eval.dnval;
  env: Eval.dnval Environment.t;
  tyenv: Syntax.ty Environment.t;
}


let test_eval env tyenv prog_str = 
  let decl = Parser.toplevel Lexer.main (Lexing.from_string prog_str) in
  let ty, new_tyenv = ty_decl tyenv decl in
  let (id, newenv, v) = eval_decl env decl in
  {ty = ty; v = v; env = newenv; tyenv = new_tyenv}

let initial_env = 
  Environment.extend "i" (IntV 1)
    (Environment.extend "v" (IntV 5) 
       (Environment.extend "x" (IntV 10) 
          (Environment.extend "uso" (BoolV false) Environment.empty)))

let initial_tyenv = 
  Environment.extend "i" TyInt
    ( Environment.extend "v" TyInt
        ( Environment.extend "x" TyInt
            ( Environment.extend "uso" TyBool Environment.empty)))

let srcfile = ref "-"

let usage = "Usage: " ^ Sys.argv.(0) ^ " [-test]"

let aspec = Arg.align [
    ("-test", Arg.Unit (fun () -> test := true),
     " run test");]

let main() = 
  Arg.parse aspec (fun s -> srcfile := s) usage;
  if !test then Test.run_test ()
  else read_eval_print initial_env initial_tyenv

let _ = main ()
