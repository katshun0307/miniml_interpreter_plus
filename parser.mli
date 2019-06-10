
(* The type of tokens. *)

type token = 
  | WITH
  | UNDERBAR
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
  | OF
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
  | FPLUS
  | FMULT
  | FMINUS
  | FLT
  | FLOATV of (float)
  | FDIVIDE
  | FALSE
  | EQ
  | ELSE
  | DIVIDE
  | DFUN
  | CONS
  | COMMA
  | BOOL
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.program)
