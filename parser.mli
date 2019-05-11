
(* The type of tokens. *)

type token = 
  | WITH
  | TYPE
  | TYID of (Syntax.tyid)
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
  | MODULO
  | MINUS
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
  | DIVIDE
  | DFUN
  | CONS
  | COMMA
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.program)
