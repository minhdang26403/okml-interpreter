(* lexer.mll *)
{
    open Parser
}

(* regex for numbers *)
let digit         = ['0'-'9']
let nat           = digit+
let num           = '-'? nat

(* regex for identifiers *)
let ident_start   = ['a'-'z' '_']
let ident_char    = ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']
let ident         = ident_start ident_char*

(* regex for whitespace *)
let whitespace    = (' ' | '\t' | '\n' | '\r')


rule tokenize     = parse
    (* let bindings *)
    | "let"         { LET }
    | "in"          { IN }

    (* functions *)
    | "fun"         { FUN }
    | "->"          { ARROW }
    | "rec"         { REC }

    (* pattern matching *)
    | "match"       { MATCH }
    | "with"        { WITH }
    | "|"           { BAR }

    (* conditional branching *)
    | "if"          { IF }
    | "then"        { THEN }
    | "else"        { ELSE }

    (* boolean literals *)
    | "true"        { TRUE }
    | "false"       { FALSE }

    (* logical operators *)
    | "&&"          { AND }
    | "||"          { OR }
    | "not"         { NOT }

    (* arithmetic operators *)
    | "+"           { PLUS }
    | "-"           { MINUS }
    | "*"           { TIMES }
    | "/"           { DIV }

    (* comparison operators *)
    | "="           { EQ }
    | "<>"          { NEQ }
    | ">="          { GEQ }
    | "<="          { LEQ }
    | ">"           { GT }
    | "<"           { LT }

    (* tuple construction *)
    | "("           { LPAREN }
    | ")"           { RPAREN }
    | ","           { COMMA }

    (* list construction *)
    | "["           { LBRACK }
    | "]"           { RBRACK }
    | "::"          { CONS }

    (* integers *)
    | num as n      { INT (int_of_string n) }

    (* identifiers *)
    | ident as id   { IDENT id }

    (* whitespace (skip) *)
    | whitespace+   { tokenize lexbuf }

    (* end-of-file *)
    | eof           { EOF }

    (* anything unexpected *)
    | _ as c        { failwith ("unexpected character: " ^ (Char.escaped c)) }
