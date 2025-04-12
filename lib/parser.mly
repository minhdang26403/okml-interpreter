
%{
    open Exp
%}

(* variables *)
%token <string> IDENT

(* let bindings and functions *)
%token LET IN FUN ARROW REC

(* integer literals *)
%token <int>INT

(* arithmetic  operators *)
%token PLUS MINUS TIMES DIV

(* comparison operators *)
%token EQ NEQ GEQ LEQ GT LT

(* boolean literals and logical operators *)
%token TRUE FALSE
%token AND OR NOT

(* conditionals *)
%token IF THEN ELSE

(* tuple construction *)
%token LPAREN RPAREN COMMA    (* for (e1, e2) *)

(* list construction *)
%token CONS                   (* for :: *)
%token LBRACK RBRACK          (* for [] and [ ] *)

(* pattern maching *)
%token MATCH WITH BAR

(* unit value *)
%token UNIT

(* end-of-file *)
%token EOF

%start <ast>parse
%%

let parse :=
    | a=exp0; EOF; { a }

let exp0 := 
    | a=exp0; PLUS; b=exp1; { BinOp (Add, a, b) }
    | a=exp1; { a }

let exp1 := 
    | a=exp1; TIMES; b=exp2; { BinOp (Mul, a, b) }
    | a=exp2; { a }

let exp2 :=
    | n=INT; { Base (Int n) } 
    | LPAREN; a=exp0; RPAREN; { a }
    
