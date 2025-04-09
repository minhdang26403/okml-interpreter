
%{
    open Exp
%}

%token PLUS TIMES

%token <int>INT

%token LPAREN RPAREN

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
    
