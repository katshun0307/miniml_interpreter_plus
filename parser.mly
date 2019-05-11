%{
open Syntax
%}

%token LPAREN RPAREN SEMISEMI
%token PLUS MINUS MULT DIVIDE MODULO LT AND OR 
%token IF THEN ELSE TRUE FALSE
%token LET IN EQ LETAND REC
%token RARROW FUN DFUN 
%token MATCH WITH CONS SQLPAREN SEMI SQRPAREN SPLIT COMMA
%token TYPE

%token <int> INTV
%token <Syntax.id> ID
%token <Syntax.tyid> TYID

%start toplevel
%type <Syntax.program> toplevel
%%

toplevel :
  | e=Expr SEMISEMI { Exp e }
  | LET x=ID EQ e=Expr SEMISEMI { Decl(x, e) }
  | LET f=ID b=LETFUNExpr { Decl(f, b) } (* declaration *)
  | LET REC f=ID EQ FUN para=ID RARROW e=Expr SEMISEMI { RecDecl(f, para, e) } (* recursive declaration 1*)
  | LET REC f=ID para=ID EQ e=Expr SEMISEMI { RecDecl(f, para, e) } (* recursive declaration 2 *)
  | TYPE ty=ID EQ decls_rest=TYDECLSExpr SEMISEMI { TypeDecl(ty, decls_rest) }

(* let function declarations *)
LETFUNExpr :
  | para=LETFUNPARAExpr e=Expr SEMISEMI { FunExp(para, e) }

LETFUNPARAExpr :
  | x=ID l=LETFUNPARAExpr { x :: l }
  | x=ID EQ { x :: [] }

(* type declarations *)
TYDECLSExpr : 
  | tv=TYID  { [tv] }
  | tv=TYID SPLIT rest=TYDECLSExpr { tv:: rest }

Expr :
  | e=IfExpr { e } (* if expression *)
  | e=EqualExpr { e } (* boolean expression *)  
  | e=LETExpr { e } (* let expression *)
  | e=LETRECExpr { e } (* recursive let expression *)
  | e=FUNExpr { e } (* static function expression *)
  | e=DFUNExpr { e } (* dynamic function expression *)
  | e=BinExpr { e } (* binary expressions *) 
  | e=MatchExpr { e } (* match expressions *)
  | e=TupleExpr { e } (* tuple expression *)

(* if expression *)
IfExpr :
  | IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) }

(* list expression *)
ListExpr : 
  | SQLPAREN c=ListContentExpr { ListExp(c) }

ListContentExpr : 
  | SQRPAREN { [] }
  | e=Expr SEMI SQRPAREN { [e] }
  | e=Expr SQRPAREN { [e] }
  | e=Expr SEMI next=ListContentExpr { e::next }

(* match expression *)
MatchExpr : 
  | MATCH ce=Expr WITH cases=ListMatchCaseExpr { MatchExp(ce, cases) }
  | MATCH ce=Expr WITH cases=TupleMatchCaseExpr { MatchExp(ce, cases) }
  | MATCH cl1=Expr COMMA cl2=Expr WITH cases=TupleMatchCaseExpr { MatchExp(TupleExp(cl1, cl2), cases) }
    
ListMatchPatternExpr :
  | hd=ID CONS rest=ListMatchPatternExpr { Cons(hd, rest) }
  | hd=ID CONS tl=ID { Cons(hd, Id tl) }
  | hd=ID CONS SQLPAREN SQRPAREN { Cons(hd, Tail) }
  | id=ID { Id(id) }
  | SQLPAREN SQRPAREN { Tail }

ListMatchCaseExpr : 
  | SPLIT p=ListMatchPatternExpr RARROW e=Expr nextcase=ListMatchCaseExpr { (ListPattern p, e)::nextcase }
  | SPLIT p=ListMatchPatternExpr RARROW e=Expr { [(ListPattern p, e)] }

TupleMatchCaseExpr :
    | SPLIT l1=ListMatchPatternExpr COMMA l2=ListMatchPatternExpr RARROW e=Expr nextcase=TupleMatchCaseExpr { (TuplePattern (l1, l2), e)::nextcase }
    | SPLIT l1=ListMatchPatternExpr COMMA l2=ListMatchPatternExpr RARROW e=Expr { [(TuplePattern (l1, l2), e)] }

(* tuple expression *)
TupleExpr : 
  | LPAREN e1=Expr COMMA e2=Expr RPAREN { TupleExp(e1, e2) } 

(* let expression *)
LETExpr :
  | LET e1=MULTILETExpr IN e2=Expr { MultiLetExp(e1, e2) } (* simple value declarations *)

LETRECExpr : 
  | LET REC f=ID EQ FUN para=ID RARROW e1=Expr IN e2=Expr { LetRecExp(f, para, e1, e2) }
  | LET REC f=ID para=ID EQ e1=Expr IN e2=Expr { LetRecExp(f, para, e1 ,e2) }

(* multiple declarations for let expression *)
MULTILETExpr : 
  /* | x=ID EQ e=Expr LETAND l=MULTILETExpr { (x, e) :: l } */
  /* | x=ID EQ e=Expr { (x, e) :: [] } */
  | x=ID EQ e=Expr LETAND l=MULTILETExpr { (x, e) :: l }
  | f=ID params=LETFUNPARAExpr e=Expr LETAND l=MULTILETExpr { (f, FunExp(params, e)) :: l }
  | x=ID EQ e=Expr { (x, e) :: [] }
  | f=ID params=LETFUNPARAExpr e=Expr { (f, FunExp(params, e)) :: [] }

/* LETEXPDECLExpr : (* <f x y x = x + y * z> / <x = 2> *)
  | x=ID EQ e=Expr { (x, e) } (* for simple declarations *)
  | f=ID params=LETFUNPARAExpr e=Expr { (f, FunExp(params, e)) } (* for function declarations using let *) */

EqualExpr : (* values equals *)
  | l=ORExpr EQ r=ORExpr { BinOp (Eq, l, r) }
  | e=ORExpr { e } 

(* logical expressions *)
ORExpr : (* or *)
  | l=ANDExpr OR r=ANDExpr { LogicOp (Or, l, r) }
  | e=ANDExpr { e }

ANDExpr : (* and *)
  | l=LTExpr AND r=ANDExpr { LogicOp (And, l, r) }
  | e=LTExpr { e }

(* number expressions *)
LTExpr : (* less than expression *)
  | l=AdditionExpr LT r=AdditionExpr { BinOp (Lt, l, r) }
  | e=AdditionExpr { e }

AdditionExpr : (* addition *)
  | l=AdditionExpr PLUS r=SubtractionExpr { BinOp (Plus, l, r) }
  | e=SubtractionExpr { e }

SubtractionExpr : (* subtraction *)
  | l=SubtractionExpr MINUS r=MultExpr { BinOp (Minus, l, r) }
  | e=MultExpr { e }

MultExpr : (* multiplication *)
  | l=MultExpr MULT r=AppExpr { BinOp (Mult, l, r) }
  | l=MultExpr DIVIDE r=AppExpr { BinOp(Div, l, r) }
  | l=MultExpr MODULO r=AppExpr { BinOp(Modulo, l, r) }
  | e=AppExpr { e }

AppExpr : (* function application *)
  | e1=AppExpr e2=AExpr { AppExp(e1, e2) }
  | e1=BinExpr e2=AExpr { AppExp(e1, e2) }
  | e=AExpr { e }

(* static function expression *)
FUNExpr : (* store ids as list *)
  | FUN params=FUNPARAExpr e=Expr { FunExp(params, e) }

FUNPARAExpr : 
  | x=ID l=FUNPARAExpr { x :: l }
  | x=ID RARROW { x :: [] }

(* dynamic function expression *)
DFUNExpr : (* dfun x1 ... -> expr *)
  | DFUN b=DFunBottomultExpr { b }

DFunBottomultExpr : (* ....xn-1 xn -> expr *)
  | x=ID RARROW e=Expr { DFunExp(x, e) }
  | x=ID b=DFunBottomultExpr { DFunExp (x, b) }

BinExpr : (* binary expression *)
  |  LPAREN EQ RPAREN   { FunExp(["a" ; "b"], BinOp   (Eq,    Var "a", Var "b")) }
  |  LPAREN PLUS RPAREN   { FunExp(["a" ; "b"], BinOp   (Plus,    Var "a", Var "b")) }
  |  LPAREN MINUS RPAREN  { FunExp(["a" ; "b"], BinOp   (Minus,   Var "a", Var "b")) }
  |  LPAREN MULT RPAREN   { FunExp(["a" ; "b"], BinOp   (Mult,    Var "a", Var "b")) }
  |  LPAREN DIVIDE RPAREN { FunExp(["a" ; "b"], BinOp   (Div,     Var "a", Var "b")) }
  |  LPAREN MODULO RPAREN { FunExp(["a" ; "b"], BinOp   (Modulo,  Var "a", Var "b")) }
  |  LPAREN LT RPAREN     { FunExp(["a" ; "b"], BinOp   (Lt,      Var "a", Var "b")) }
  |  LPAREN AND RPAREN    { FunExp(["a" ; "b"], LogicOp (And,     Var "a", Var "b")) }
  |  LPAREN OR RPAREN     { FunExp(["a" ; "b"], LogicOp (Or,      Var "a", Var "b")) }

(* most basic expressions *)
AExpr : (* integer, boolean, variable(id), expression_with_parenthesis *)
  | i=INTV { ILit i } 
  | e=ListExpr { e }
  | TRUE   { BLit true }
  | FALSE  { BLit false }
  | i=ID   { Var i }
  | i=TYID { UserExp i }
  | LPAREN e=Expr RPAREN { e }
