(* parser.mly *)
%{
  open Exp
%}


(* token definitions *)
%token LET IN                 (* let bindings *)
%token FUN ARROW REC          (* functions *)
%token MATCH WITH BAR         (* pattern matching *)
%token IF THEN ELSE           (* conditional branching *)
%token TRUE FALSE             (* boolean literals *)
%token AND OR NOT             (* logical operators *)
%token PLUS MINUS TIMES DIV   (* arithmetic operators *)
%token EQ NEQ GEQ LEQ GT LT   (* comparison operators *)
%token LPAREN RPAREN COMMA    (* tuple construction *)
%token LBRACK RBRACK CONS     (* list construction *)
%token <int> INT              (* integers *)
%token <string> IDENT         (* identifiers *)
%token EOF                    (* identifiers *)


(* type declarations *)
%type <ast> expr
%type <ast -> ast> match_expr
%type <ast> logic_or
%type <ast> logic_and
%type <ast> comparison
%type <ast> list_cons
%type <ast> arith_add_sub
%type <ast> arith_mul_div
%type <ast> unary
%type <ast> func_app
%type <ast> primary
%type <unit option> option(BAR)


(* entry point *)
%start <ast> parse
%%

parse:
  | e=expr EOF { e }

expr:
  (* function abstraction *)
  | FUN x=IDENT ARROW e=expr { UnOp (Fun x, e) }

  (* let binding *)
  | LET x=IDENT EQ e1=expr IN e2=expr { BinOp (Let x, e1, e2) }
  | LET REC f=IDENT x=IDENT EQ e1=expr IN e2=expr { BinOp(LetRec (f, x), e1, e2) }

  (* pattern matching *)
  | MATCH e=expr WITH m=match_expr { m e }

  (* conditional branching *)
  | IF e1=expr THEN e2=expr ELSE e3=expr { TrinOp (Cond, e1, e2, e3) }

  (* higher-precedence expression *)
  | e=logic_or { e }

match_expr:
  (* pair matching *)
  | BAR? LPAREN x=IDENT COMMA y=IDENT RPAREN ARROW e2=expr
      { fun e1 -> BinOp (MatchP (x, y), e1, e2) }

  (* list matching (two possible orders) *)
  | BAR? LBRACK RBRACK ARROW e2=expr     (* empty list case first *)
    BAR x=IDENT CONS xs=IDENT ARROW e3=expr
      { fun e1 -> TrinOp (MatchL (x, xs), e1, e2, e3) }

  | BAR? x=IDENT CONS xs=IDENT ARROW e3=expr
    BAR LBRACK RBRACK ARROW e2=expr      (* empty list case second *)
      { fun e1 -> TrinOp (MatchL (x, xs), e1, e2, e3) }

logic_or:
  | e1=logic_and OR e2=logic_or       { BinOp (Or, e1, e2) }
  | e=logic_and                       { e }

logic_and:
  | e1=comparison AND e2=logic_and    { BinOp (And, e1, e2) }
  | e=comparison                      { e }

comparison:
  | e1=comparison EQ e2=list_cons     { BinOp (Eq, e1, e2) }
  | e1=comparison NEQ e2=list_cons    { BinOp (Neq, e1, e2) }
  | e1=comparison GEQ e2=list_cons    { BinOp (Geq, e1, e2) }
  | e1=comparison LEQ e2=list_cons    { BinOp (Leq, e1, e2) }
  | e1=comparison GT e2=list_cons     { BinOp (Gt, e1, e2) }
  | e1=comparison LT e2=list_cons     { BinOp (Lt, e1, e2) }
  | e=list_cons                       { e }

list_cons:
  | e1=arith_add_sub CONS e2=list_cons    { BinOp (Cons, e1, e2) }
  | e=arith_add_sub                       { e }

arith_add_sub:
  | e1=arith_add_sub PLUS e2=arith_mul_div    { BinOp (Add, e1, e2) }
  | e1=arith_add_sub MINUS e2=arith_mul_div   { BinOp (Sub, e1, e2) }
  | e=arith_mul_div                           { e }

arith_mul_div:
  | e1=arith_mul_div TIMES e2=unary   { BinOp (Mul, e1, e2) }
  | e1=arith_mul_div DIV e2=unary     { BinOp (Div, e1, e2) }
  | e=unary                           { e }

unary:
  | MINUS e=unary   { UnOp (Neg, e) }
  | NOT e=unary     { UnOp (Not, e) }
  | e=func_app      { e }

func_app:
  | e1=func_app e2=primary    { BinOp (App, e1, e2) }
  | e=primary                 { e }

primary:
  | x=IDENT                             { Base (Var x) }
  | n=INT                               { Base (Int n) }
  | TRUE                                { Base (Bool true) }
  | FALSE                               { Base (Bool false) }
  | LPAREN RPAREN                       { Base Unit }
  | LBRACK RBRACK                       { Base Nil }
  | LPAREN e=expr RPAREN                { e }
  | LPAREN e1=expr COMMA e2=expr RPAREN { BinOp (Pair, e1, e2) }
