
(* The type of tokens. *)

type token = 
  | WITH
  | TRUE
  | THEN
  | SQRPAREN
  | SQLPAREN
  | SPLIT
  | SEMISEMI
  | SEMI
  | RPAREN
  | REC
  | RARROW
  | PLUS
  | OR
  | MULT
  | MATCH
  | LT
  | LPAREN
  | LETAND
  | LET
  | INTV of (int)
  | IN
  | IF
  | ID of (Syntax.id)
  | FUN
  | FALSE
  | EQ
  | ELSE
  | DFUN
  | CONS
  | COMMA
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.program)
