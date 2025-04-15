(* parser.mly *)
%{
    open Exp
%}

(* variables *)
%token IDENT

(* let bindings and functions *)
%token LET IN FUN ARROW REC

(* integer literals *)
%token INT

(* arithmetic operators *)
%token PLUS MINUS TIMES DIV

(* comparison operators *)
%token EQ NEQ GEQ LEQ GT LT

(* boolean literals and logical operators *)
%token TRUE FALSE %token AND OR NOT

(* conditionals *)
%token IF THEN ELSE

(* tuple construction *)
%token LPAREN RPAREN COMMA

(* list construction *)
%token CONS %token LBRACK RBRACK

(* pattern matching *)
%token MATCH WITH BAR

(* unit value *)
%token UNIT

(* end-of-file *)
%token EOF

(* Type declarations *)
%type <Exp.ast> parse
%type <Exp.ast> expr
%type <Exp.ast -> Exp.ast> match_expr
%type <Exp.ast> logic_or
%type <Exp.ast> logic_and
%type <Exp.ast> compare
%type <Exp.ast> cons
%type <Exp.ast> arith_add
%type <Exp.ast> arith_mul
%type <Exp.ast> unary
%type <Exp.ast> app
%type <Exp.ast> atom

%start parse
%%

parse:
  | e=expr; EOF { e }

expr:
  | LET x=IDENT EQ e1=expr IN e2=expr               { BinOp (Let x, e1, e2) }
  | FUN x=IDENT ARROW e=expr                        { UnOp (Fun x, e) }
  | LET REC f=IDENT x=IDENT EQ e1=expr IN e2=expr   { BinOp (LetRec (f, x), e1, e2) }
  | IF c=expr THEN t=expr ELSE f=expr               { TrinOp (Cond, c, t, f) }
  | MATCH e=expr WITH m=match_expr                  { m e }
  | e=logic_or                                      { e }

logic_or:
  | a=logic_and OR b=logic_or  { BinOp (Or, a, b) }
  | a=logic_and                { a }

logic_and:
  | a=compare AND b=logic_and  { BinOp (And, a, b) }
  | a=compare                  { a }

compare:
  | a=compare EQ b=cons        { BinOp (Eq, a, b) }
  | a=compare NEQ b=cons       { BinOp (Neq, a, b) }
  | a=compare GEQ b=cons       { BinOp (Geq, a, b) }
  | a=compare LEQ b=cons       { BinOp (Leq, a, b) }
  | a=compare GT b=cons        { BinOp (Gt, a, b) }
  | a=compare LT b=cons        { BinOp (Lt, a, b) }
  | a=cons                     { a }

cons:
  | hd=arith_add CONS tl=cons  { BinOp (Cons, hd, tl) }
  | e=arith_add                { e }

arith_add:
  | a=arith_add PLUS b=arith_mul   { BinOp (Add, a, b) }
  | a=arith_add MINUS b=arith_mul  { BinOp (Sub, a, b) }
  | a=arith_mul                    { a }

arith_mul:
  | a=arith_mul TIMES b=unary      { BinOp (Mul, a, b) }
  | a=arith_mul DIV b=unary        { BinOp (Div, a, b) }
  | a=unary                        { a }

unary:
  | MINUS e=unary     { UnOp (Neg, e) }
  | NOT e=unary       { UnOp (Not, e) }
  | e=app             { e }

app:
  | f=app arg=atom    { BinOp (App, f, arg) }
  | e=atom            { e }

atom:
  | n=INT                                { Base (Int n) }
  | TRUE                                 { Base (Bool true) }
  | FALSE                                { Base (Bool false) }
  | x=IDENT                              { Base (Var x) }
  | UNIT                                 { Base Unit }
  | LPAREN e1=expr COMMA e2=expr RPAREN { BinOp (Pair, e1, e2) }
  | LPAREN e=expr RPAREN                { e }
  | LBRACK RBRACK                       { Base Nil }

match_expr:
  | BAR LBRACK; RBRACK; ARROW e1=expr;
    BAR x=IDENT; CONS; xs=IDENT; ARROW e2=expr
      { fun e -> TrinOp (MatchL (x, xs), e, e1, e2) }

  | BAR x=IDENT; CONS; xs=IDENT; ARROW e2=expr;
    BAR LBRACK; RBRACK; ARROW e1=expr
      { fun e -> TrinOp (MatchL (x, xs), e, e1, e2) }

  | BAR LPAREN; x=IDENT; COMMA; y=IDENT; RPAREN; ARROW e=expr
      { fun e0 -> BinOp (MatchP (x, y), e0, e) }
