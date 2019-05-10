
(* The type of tokens. *)

type token = 
  | WITH
  | UNDERBAR
  | TYID of (Syntax.tyid)
  | TRUE
  | THEN
  | STRV of (Syntax.raw_str)
  | STRING
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
  | LIST
  | LETAND
  | LET
  | INTV of (int)
  | INT
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
  | COLON
  | BOOL
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.program)
