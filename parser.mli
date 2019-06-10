
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
  | RCURLY
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
  | LCURLY
  | INT_OF_FLOAT
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
  | FLOAT_OF_INT
  | FLOATV of (float)
  | FDIVIDE
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
