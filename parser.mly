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
%token REF ASSIGN DEASSIGN MUTABLE MUTE

%token <int> INTV
%token <float> FLOATV
%token <Syntax.id> ID
%token <Syntax.tyid> TYID
%token <Syntax.tyvar_annot> TYVARANNOT

%start toplevel
%type <Syntax.program> toplevel
%%

toplevel :
  | e=Expr SEMISEMI { Exp e }
  | LET x=ID EQ e=Expr SEMISEMI { Decl((x, None), e) }
  | LET  x=ID COLON ty=TypeExpr EQ e=Expr SEMISEMI { Decl((x, Some ty), e) }
  | LET x=AnnotIdExpr EQ e=Expr SEMISEMI { Decl(x, e) }
  | LET f=ID b=LETFUNExpr { Decl((f, None), b) } (* declaration *)
  | LET REC f=ID EQ FUN para=ID RARROW e=Expr SEMISEMI { RecDecl(f, para, e) } (* recursive declaration 1*)
  | LET REC f=ID para=ID EQ e=Expr SEMISEMI { RecDecl(f, para, e) } (* recursive declaration 2 *)
  | TYPE ty=ID EQ decls_rest=TYDECLSExpr SEMISEMI { VariantDecl(None, ty, decls_rest) } (* variant declaration *)
  | TYPE s=TYVARANNOT ty=ID EQ decls_rest=TYDECLSExpr SEMISEMI { VariantDecl(Some s, ty, decls_rest) } (* variant declaration *)
  | TYPE recname=ID EQ LCURLY fields=FieldsDeclExpr SEMISEMI { RecordDecl(None, recname, fields) }
  | TYPE s=TYVARANNOT recname=ID EQ LCURLY fields=FieldsDeclExpr SEMISEMI { RecordDecl(Some s, recname, fields) }

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
  | LPAREN e=Expr COLON ty=TypeExpr RPAREN { Annotated(e, ty) }
  | i=ID ASSIGN e=Expr { Assign(i, e) }
  | e1=Expr DOT field=ID MUTE e2=Expr { RecordMuteExp(e1, field, e2) } 
  | DEASSIGN e=Expr { Deassign e }

TypeExpr :
  | INT { TyInt }
  | BOOL { TyBool }
  | FLOAT { TyFloat }
  | i=ID { TyUser i }
  | e=TyVarTypeExpr { e }
  | a=TypeExpr RARROW b=TypeExpr { TyFun(a, b) }
  | lty=TypeExpr LIST { TyList lty }
  | a=TypeExpr MULT b=TypeExpr { TyTuple(a, b) }
  | ty=TypeExpr i=ID { TyParaUser(ty, i) }
  | ty=TypeExpr REF { TyRef(ty) }
  | LPAREN e=TypeExpr RPAREN { e }

TyVarTypeExpr : 
  | s=TYVARANNOT { TyVar(fresh_tyvar_annot s) }

(* let function declarations *)
(* ex: let f x y = x + y *)
LETFUNExpr :
  | para=LETFUNPARAExpr e=Expr SEMISEMI { FunExp(para, e) }

LETFUNPARAExpr :
  | x=AnnotIdExpr l=LETFUNPARAExpr { x :: l }
  | x=AnnotIdExpr EQ { x :: [] }

(* let expression *)
(* ex: let x = 3 and y = 5 in x + y *)
LETExpr :
  | LET e1=MULTILETExpr IN e2=Expr { MultiLetExp(e1, e2) } (* simple value declarations *)

MULTILETExpr : 
  | x=ID EQ e=Expr LETAND l=MULTILETExpr { ((x, None), e) :: l }
  | x=ID EQ e=Expr { ((x, None), e) :: [] }
  | x=ID COLON ty=TypeExpr EQ e=Expr LETAND l=MULTILETExpr { ((x, Some ty), e) :: l }
  | x=ID COLON ty=TypeExpr EQ e=Expr { ((x, Some ty), e) :: [] }
  | x=AnnotIdExpr EQ e=Expr LETAND l=MULTILETExpr { (x, e) :: l }
  | x=AnnotIdExpr EQ e=Expr { (x, e) :: [] }
  | f=ID params=LETFUNPARAExpr e=Expr LETAND l=MULTILETExpr { ((f, None), FunExp(params, e)) :: l }
  | f=ID params=LETFUNPARAExpr e=Expr { ((f, None), FunExp(params, e)) :: [] }

(* let rec expression *)
LETRECExpr : 
  | LET REC f=ID EQ FUN para=ID RARROW e1=Expr IN e2=Expr { LetRecExp(f, para, e1, e2) }
  | LET REC f=ID para=ID EQ e1=Expr IN e2=Expr { LetRecExp(f, para, e1 ,e2) }

(* type declarations *)
TYDECLSExpr : 
  | variant=TYID  { [(variant, TyDummy)] }
  | variant=TYID OF t=TypeExpr { [(variant, t)] }
  | variant=TYID SPLIT rest=TYDECLSExpr { (variant, TyDummy) :: rest }
  | variant=TYID OF t=TypeExpr SPLIT rest=TYDECLSExpr { (variant, t)::rest }

(* record declarations *)
FieldsDeclExpr : 
  | fieldname=ID COLON t=TypeExpr RCURLY { [(fieldname, t, false)] }
  | fieldname=ID COLON t=TypeExpr SEMI RCURLY { [(fieldname, t, false)] }
  | fieldname=ID COLON t=TypeExpr SEMI rest=FieldsDeclExpr { (fieldname, t, false):: rest }
  | MUTABLE fieldname=ID COLON t=TypeExpr RCURLY { [(fieldname, t, true)] }
  | MUTABLE fieldname=ID COLON t=TypeExpr SEMI RCURLY { [(fieldname, t, true)] }
  | MUTABLE fieldname=ID COLON t=TypeExpr SEMI rest=FieldsDeclExpr { (fieldname, t, true):: rest }

(* use records *)
RecordExpr : 
  | LCURLY content=RecordContentExpr { let tyref = ref "-" in RecordExp(tyref, content) }

RecordContentExpr : 
  | fieldname=ID EQ content=Expr RCURLY { let mut_ref = ref false in [(fieldname, content, mut_ref)] }
  | fieldname=ID EQ content=Expr SEMI RCURLY { let mut_ref = ref false in [(fieldname, content, mut_ref)] }
  | fieldname=ID EQ content=Expr SEMI rest=RecordContentExpr { let mut_ref = ref false in (fieldname, content, mut_ref):: rest }

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
  | vari=TYID e2=AExpr { AppExp(Var (VARIANT vari), e2) }
  | e1=Expr DOT fieldname=ID { RecordAppExp(e1, fieldname) }
  | e=AExpr { e }

(* static function expression *)
FUNExpr : (* store ids as list *)
  | FUN params=FUNPARAExpr e=Expr { FunExp(params, e) }

FUNPARAExpr : 
  | x=AnnotIdExpr l=FUNPARAExpr { x :: l }
  | x=AnnotIdExpr RARROW { x :: [] }

(* dynamic function expression *)
DFUNExpr : (* dfun x1 ... -> expr *)
  | DFUN b=DFunBottomultExpr { b }

DFunBottomultExpr : (* ....xn-1 xn -> expr *)
  | x=ID RARROW e=Expr { DFunExp(x, e) }
  | x=ID b=DFunBottomultExpr { DFunExp (x, b) }

BinExpr : (* binary expression *)
  |  LPAREN EQ RPAREN      { FunExp([("a", None) ; ("b", None)], BinOp   (Eq,      Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN PLUS RPAREN    { FunExp([("a", None) ; ("b", None)], BinOp   (Plus,    Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN MINUS RPAREN   { FunExp([("a", None) ; ("b", None)], BinOp   (Minus,   Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN MULT RPAREN    { FunExp([("a", None) ; ("b", None)], BinOp   (Mult,    Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN DIVIDE RPAREN  { FunExp([("a", None) ; ("b", None)], BinOp   (Div,     Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN MODULO RPAREN  { FunExp([("a", None) ; ("b", None)], BinOp   (Modulo,  Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN LT RPAREN      { FunExp([("a", None) ; ("b", None)], BinOp   (Lt,      Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN AND RPAREN     { FunExp([("a", None) ; ("b", None)], LogicOp (And,     Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN OR RPAREN      { FunExp([("a", None) ; ("b", None)], LogicOp (Or,      Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN FPLUS RPAREN   { FunExp([("a", None) ; ("b", None)], BinOp   (FPlus,   Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN FMINUS RPAREN  { FunExp([("a", None) ; ("b", None)], BinOp   (FMinus,  Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN FMULT RPAREN   { FunExp([("a", None) ; ("b", None)], BinOp   (FMult,   Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN FDIVIDE RPAREN { FunExp([("a", None) ; ("b", None)], BinOp   (FDiv,    Var (ID ("a", None)), Var (ID ("b", None)))) }
  |  LPAREN FLT RPAREN     { FunExp([("a", None) ; ("b", None)], BinOp   (FLt,     Var (ID ("a", None)), Var (ID ("b", None)))) }

(* most basic expressions *)
AExpr : (* integer, boolean, variable(id), expression_with_parenthesis *)
  | i=INTV { ILit i } 
  | f=FLOATV { FLit f }
  | e=ListExpr { e }
  | TRUE   { BLit true }
  | FALSE  { BLit false }
  /* | i=ID { Var(ID (i, None)) } */
  | i=TYID { Var (VARIANT i) }
  | LPAREN e=Expr RPAREN { e }
  | REF e=Expr { Reference e } 
  | e=AnnotIdExpr { Var(ID e) } (* includes non annotated ids *)

AnnotIdExpr : 
  /* | i=ID COLON ty=TypeExpr { (i, Some ty) } */
  | LPAREN i=ID COLON ty=TypeExpr RPAREN { (i, Some ty) }
  | LPAREN e=AnnotIdExpr RPAREN { e }
  | i=ID { (i, None) }
