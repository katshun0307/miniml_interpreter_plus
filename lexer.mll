{
let reservedWords = [
  (* Keywords *)
  ("else", Parser.ELSE);
  ("false", Parser.FALSE);
  ("if", Parser.IF);
  ("then", Parser.THEN);
  ("true", Parser.TRUE);
  ("let", Parser.LET);
  ("rec", Parser.REC);
  ("in", Parser.IN);
  ("fun", Parser.FUN);
  ("dfun", Parser.DFUN);
  ("and", Parser.LETAND);
  ("match", Parser.MATCH);
  ("with", Parser.WITH);
  ("int", Parser.INT);
  ("bool", Parser.BOOL);
  ("list", Parser.LIST);
  ("type", Parser.TYPE);
  ("of", Parser.OF);
] 
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012' '\n']+     { main lexbuf }

| "(*" { comment 1 lexbuf } 

| "-"? ['0'-'9']+
    { Parser.INTV (int_of_string (Lexing.lexeme lexbuf)) }

| "-"? ['0'-'9']+ "." ['0'-'9']*
    { Parser.FLOATV (float_of_string (Lexing.lexeme lexbuf)) }

| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| ";;" { Parser.SEMISEMI }
| "+." { Parser.FPLUS }
| "-." { Parser.FMINUS }
| "*." { Parser.FMULT }
| "/." { Parser.FDIVIDE }
| "<." { Parser.FLT }
| "+" { Parser.PLUS }
| "-" { Parser.MINUS }
| "*" { Parser.MULT }
| "/" { Parser.DIVIDE }
| "%" { Parser.MODULO }
| "<" { Parser.LT }
| "&&" { Parser.AND }
| "||" { Parser.OR }
| "=" { Parser.EQ }
| "->" { Parser.RARROW }
| "[" { Parser.SQLPAREN }
| ";" { Parser.SEMI }
| "]" { Parser.SQRPAREN }
| "|" { Parser.SPLIT }
| "::" { Parser.CONS }
| "," { Parser.COMMA }
| "_" { Parser.UNDERBAR }
| ['a'-'z'] ['a'-'z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      try 
        List.assoc id reservedWords
      with
      _ -> Parser.ID id
     }
| ['A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_' '\'']*
    { let tyid = Lexing.lexeme lexbuf in
      Parser.TYID tyid
     }
| eof { exit 0 }

and comment i = parse
| "*)" { if i = 1 then main lexbuf else comment (i-1) lexbuf } 
| "(*" { comment (i+1) lexbuf }
| _ {comment i lexbuf}
