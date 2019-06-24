%{
open Syntax
%}

%token LPAREN RPAREN SEMISEMI
%token PLUS MINUS MULT DIVIDE MODULO LT AND OR
%token FPLUS FMINUS FMULT FDIVIDE FLT INT_OF_FLOAT FLOAT_OF_INT
%token IF THEN ELSE TRUE FALSE
%token LET IN EQ LETAND REC
%token RARROW FUN DFUN
%token MATCH WITH CONS SQLPAREN SEMI SQRPAREN SPLIT COMMA
%token INT BOOL LIST UNDERBAR FLOAT
%token TYPE OF COLON LCURLY RCURLY DOT

%token <int> INTV
%token <float> FLOATV
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
  | TYPE recname=ID EQ LCURLY fields=FieldsDeclExpr SEMISEMI { RecordDecl(recname, fields) }

TypeExpr :
  | INT { TyInt }
  | BOOL { TyBool }
  | FLOAT { TyFloat }
  | i=ID { TyUser i }
  | a=TypeExpr RARROW b=TypeExpr { TyFun(a, b) }
  | lty=TypeExpr LIST { TyList lty }
  | a=TypeExpr MULT b=TypeExpr { TyTuple(a, b) }
  | LPAREN e=TypeExpr RPAREN { e }

(* let function declarations *)
LETFUNExpr :
  | para=LETFUNPARAExpr e=Expr SEMISEMI { FunExp(para, e) }

LETFUNPARAExpr :
  | x=ID l=LETFUNPARAExpr { x :: l }
  | x=ID EQ { x :: [] }

(* type declarations *)
TYDECLSExpr : 
  | variant=TYID  { [(variant, TyDummy)] }
  | variant=TYID OF t=TypeExpr { [(variant, t)] }
  | variant=TYID SPLIT rest=TYDECLSExpr { (variant, TyDummy) :: rest }
  | variant=TYID OF t=TypeExpr SPLIT rest=TYDECLSExpr { (variant, t)::rest }

(* record declarations *)
FieldsDeclExpr : 
  | fieldname=ID COLON t=TypeExpr RCURLY { [(fieldname, t)] }
  | fieldname=ID COLON t=TypeExpr SEMI RCURLY { [(fieldname, t)] }
  | fieldname=ID COLON t=TypeExpr SEMI rest=FieldsDeclExpr { (fieldname, t):: rest }

Expr :
  | e=IfExpr { e } (* if expression *)
  | e=ORExpr { e } (* boolean expression *)  
  | e=LETExpr { e } (* let expression *)
  | e=LETRECExpr { e } (* recursive let expression *)
  | e=FUNExpr { e } (* static function expression *)
  | e=DFUNExpr { e } (* dynamic function expression *)
  | e=BinExpr { e } (* binary expressions *) 
  | e=MatchExpr { e } (* match expressions *)
  | e=TupleExpr { e } (* tuple expression *)
  | e=RecordExpr { e } (* record expression *)

(* use records *)
RecordExpr : 
  | LCURLY content=RecordContentExpr { RecordExp(content) }

RecordContentExpr : 
  | fieldname=ID EQ content=Expr RCURLY { [(fieldname, content)] }
  | fieldname=ID EQ content=Expr SEMI RCURLY { [(fieldname, content)] }
  | fieldname=ID EQ content=Expr SEMI rest=RecordContentExpr { (fieldname, content):: rest }

(* if expression *)
IfExpr :
  | IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) }

(* list expression *)
ListExpr : 
  | SQLPAREN c=ListContentExpr { ListExp(c) }

ListContentExpr : 
  | SQRPAREN { [] }
  | e=Expr SQRPAREN { [e] }
  | e=Expr SEMI next=ListContentExpr { e::next }

(* match expression *)
MatchExpr : 
  | MATCH ce=Expr WITH cases=MultMatchCasesExpr { MatchExp(ce, cases) }
  | MATCH ce=Expr WITH SPLIT cases=MultMatchCasesExpr { MatchExp(ce, cases) }
  /* | MATCH ce=Expr WITH fp=MatchCaseExpr1 RARROW e=Expr restcase=MultMatchCasesExpr { MatchExp(ce, (fp, e)::restcase) } */

MultMatchCasesExpr : 
  | p=MatchCaseExpr1 RARROW e=Expr SPLIT nextcase=MultMatchCasesExpr { (p, e)::nextcase }
  | p=MatchCaseExpr1 RARROW e=Expr { [(p, e)] }

MatchCaseExpr1 : (* a single pattern *)
  | t1=MatchCaseExpr1 COMMA t2=MatchCaseExpr1 { TuplePattern (t1, t2) } 
  | LPAREN t1=MatchCaseExpr1 COMMA t2=MatchCaseExpr1 RPAREN { TuplePattern (t1, t2) }
  | t=MatchCaseExpr2 { t } 

MatchCaseExpr2 :
  | h=MatchCaseExpr3 CONS t=MatchCaseExpr2 { ConsListPattern (h, t) }
  | var=TYID vv=MatchCaseExpr1 { VariantPattern (var, vv) }
  | LCURLY content=RecordMatchTailExpr { let (l, f) = content in RecordPattern(l, f) }
  | e=MatchCaseExpr3 { e }

MatchCaseExpr3 :
  | SQLPAREN SQRPAREN { TailListPattern }
  | id=ID { IdPattern id }
  | tid=TYID { SingleVariantPattern tid }
  | UNDERBAR { UnderbarPattern }

RecordMatchTailExpr : 
  | UNDERBAR RCURLY { ([], true) }
  | UNDERBAR SEMI RCURLY { ([], true) }
  | fieldname=ID EQ pattern=MatchCaseExpr1 RCURLY { ([(fieldname, pattern)], false) }
  | fieldname=ID EQ pattern=MatchCaseExpr1 SEMI RCURLY { ([(fieldname, pattern)], false) }
  | UNDERBAR SEMI rest=RecordMatchTailExpr { let (l, _) = rest in (l, true) }
  | fieldname=ID EQ pattern=MatchCaseExpr1 SEMI rest=RecordMatchTailExpr { let (l, f) = rest in ((fieldname, pattern):: l, f) }

(* tuple expression *)
TupleExpr : 
  | e1=Expr COMMA e2=Expr { TupleExp(e1, e2) } 
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

(* logical expressions *)
ORExpr : (* or *)
  | l=ORExpr OR r=ANDExpr { LogicOp (Or, l, r) }
  | e=ANDExpr { e }

ANDExpr : (* and *)
  | l=ANDExpr AND r=EqualExpr { LogicOp (And, l, r) }
  | e=EqualExpr { e }

EqualExpr : 
  | l=EqualExpr EQ r=LTExpr { BinOp (Eq, l, r) }
  | e=LTExpr { e }

(* number expressions *)
LTExpr : (* less than expression *)
  | l=LTExpr LT r=AdditionExpr { BinOp (Lt, l, r) }
  | l=LTExpr FLT r=AdditionExpr { BinOp (FLt, l, r) }
  | e=AdditionExpr { e }

AdditionExpr : (* addition *)
  | l=AdditionExpr PLUS r=SubtractionExpr { BinOp (Plus, l, r) }
  | l=AdditionExpr FPLUS r=SubtractionExpr { BinOp (FPlus, l, r) }
  | FLOAT_OF_INT e=AdditionExpr { Float_of_int e }
  | INT_OF_FLOAT e=AdditionExpr { Int_of_float e }
  | e=SubtractionExpr { e }

SubtractionExpr : (* subtraction *)
  | l=SubtractionExpr MINUS r=MultExpr { BinOp (Minus, l, r) }
  | l=SubtractionExpr FMINUS r=MultExpr { BinOp (FMinus, l, r) }
  | e=MultExpr { e }

MultExpr : (* multiplication *)
  | l=MultExpr MULT r=AppExpr { BinOp(Mult, l, r) }
  | l=MultExpr FMULT r=AppExpr { BinOp(FMult, l, r) }
  | l=MultExpr DIVIDE r=AppExpr { BinOp(Div, l, r) }
  | l=MultExpr FDIVIDE r=AppExpr { BinOp(FDiv, l, r) }
  | l=MultExpr MODULO r=AppExpr { BinOp(Modulo, l, r) }
  | e=AppExpr { e }

AppExpr : (* function application *)
  | e1=AppExpr e2=AExpr { AppExp(e1, e2) }
  | e1=BinExpr e2=AExpr { AppExp(e1, e2) }
  | vari=TYID e2=Expr { AppExp(Var (VARIANT vari), e2) }
  | e1=AppExpr DOT fieldname=ID { RecordAppExp(e1, fieldname) }
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
  |  LPAREN EQ RPAREN      { FunExp(["a" ; "b"], BinOp   (Eq,      Var (ID "a"), Var (ID "b"))) }
  |  LPAREN PLUS RPAREN    { FunExp(["a" ; "b"], BinOp   (Plus,    Var (ID "a"), Var (ID "b"))) }
  |  LPAREN MINUS RPAREN   { FunExp(["a" ; "b"], BinOp   (Minus,   Var (ID "a"), Var (ID "b"))) }
  |  LPAREN MULT RPAREN    { FunExp(["a" ; "b"], BinOp   (Mult,    Var (ID "a"), Var (ID "b"))) }
  |  LPAREN DIVIDE RPAREN  { FunExp(["a" ; "b"], BinOp   (Div,     Var (ID "a"), Var (ID "b"))) }
  |  LPAREN MODULO RPAREN  { FunExp(["a" ; "b"], BinOp   (Modulo,  Var (ID "a"), Var (ID "b"))) }
  |  LPAREN LT RPAREN      { FunExp(["a" ; "b"], BinOp   (Lt,      Var (ID "a"), Var (ID "b"))) }
  |  LPAREN AND RPAREN     { FunExp(["a" ; "b"], LogicOp (And,     Var (ID "a"), Var (ID "b"))) }
  |  LPAREN OR RPAREN      { FunExp(["a" ; "b"], LogicOp (Or,      Var (ID "a"), Var (ID "b"))) }
  |  LPAREN FPLUS RPAREN   { FunExp(["a" ; "b"], BinOp   (FPlus,   Var (ID "a"), Var (ID "b"))) }
  |  LPAREN FMINUS RPAREN  { FunExp(["a" ; "b"], BinOp   (FMinus,  Var (ID "a"), Var (ID "b"))) }
  |  LPAREN FMULT RPAREN   { FunExp(["a" ; "b"], BinOp   (FMult,   Var (ID "a"), Var (ID "b"))) }
  |  LPAREN FDIVIDE RPAREN { FunExp(["a" ; "b"], BinOp   (FDiv,    Var (ID "a"), Var (ID "b"))) }
  |  LPAREN FLT RPAREN     { FunExp(["a" ; "b"], BinOp   (FLt,     Var (ID "a"), Var (ID "b"))) }

(* most basic expressions *)
AExpr : (* integer, boolean, variable(id), expression_with_parenthesis *)
  | i=INTV { ILit i } 
  | f=FLOATV { FLit f }
  | e=ListExpr { e }
  | TRUE   { BLit true }
  | FALSE  { BLit false }
  | i=ID   { Var (ID i) }
  | i=TYID { Var (VARIANT i) }
  | LPAREN e=Expr RPAREN { e }
