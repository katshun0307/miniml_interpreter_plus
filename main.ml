open Syntax
open Eval
open Typing
open Str

let test = ref false
let load_file = ref "-"

let rec load_prog_list env tyenv l =
  match l with
  | phrase :: rest -> 
    (try
       let decl = Parser.toplevel Lexer.main (Lexing.from_string (phrase ^ ";;")) in
       let ty, new_tyenv = ty_decl tyenv decl  in
       let (id, newenv, v) = eval_decl env decl in
       Printf.printf "val %s : " id;
       print_string (string_of_ty (renumber_ty (ty_of_tysc ty)));
       print_string " = ";
       pp_val v;
       print_newline();
       load_prog_list newenv new_tyenv rest
     with e ->
       let msg = Printexc.to_string e in
       print_string ("there was an error: " ^ msg ^ "\n");
       load_prog_list env tyenv rest)
  | [] -> env, tyenv

let rec read_eval_print env tyenv =
  print_string "# ";
  flush stdout;
  try
    let decl = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
    let tysc, new_tyenv = ty_decl tyenv decl in
    let (id, newenv, v) = eval_decl env decl in
    Printf.printf "val %s : " id;
    print_string (string_of_ty (renumber_ty (ty_of_tysc tysc)));
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

let initial_env = Environment.empty
let initial_tyenv = Environment.empty
let initial_tytyenv = Environment.empty

let srcfile = ref "-"

let usage = "Usage: " ^ Sys.argv.(0) ^ " [-test] [-load <filename>]"

let aspec = Arg.align [
    ("-test", Arg.Unit (fun () -> test := true),
     " run test");
    ("-load", Arg.Set_string load_file, 
     "load program before starting REPL")]

let main() = 
  Arg.parse aspec (fun s -> srcfile := s) usage;
  if !test then Test.run_test ()
  else if !load_file = "-" then
    read_eval_print initial_env initial_tyenv
  else 
    let program_str = Core.In_channel.read_all !load_file in
    let prog_str_list = Str.split (Str.regexp ";;") program_str in
    let new_env, new_tyenv = load_prog_list initial_env initial_tyenv prog_str_list in
    read_eval_print new_env new_tyenv

let _ = main ()
