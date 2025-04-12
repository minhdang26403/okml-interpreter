
{
    open Parser
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z' '_' '\'']
let ident_start = ['a'-'z' '_']
let ident_char = ['a'-'z' 'A'-'Z' '_' '\'']
let whitespace = (' ' | '\t' | '\n' | '\r')

let nat = digit+
let num = '-'? nat

rule tokenize = parse
    (* keywords *)
    | "let"      { LET }
    | "in"       { IN }
    | "fun"      { FUN }
    | "rec"      { REC }
    | "true"     { TRUE }
    | "false"    { FALSE }
    | "not"      { NOT }
    | "&&"       { AND }
    | "||"       { OR }
    | "if"       { IF }
    | "then"     { THEN }
    | "else"     { ELSE }
    | "match"    { MATCH }
    | "with"     { WITH }
    
    (* symbols and operators *)
    | "+"        { PLUS }
    | "-"        { MINUS }
    | "*"        { TIMES }
    | "/"        { DIV }
    | "="        { EQ }
    | "<>"       { NEQ }
    | ">="       { GEQ }
    | "<="       { LEQ }
    | ">"        { GT }
    | "<"        { LT }
    | "("        { LPAREN }
    | ")"        { RPAREN }
    | ","        { COMMA }
    | "::"       { CONS }
    | "["        { LBRACK }
    | "]"        { RBRACK }
    | "->"       { ARROW }
    | "|"        { BAR }
    
    (* special case: unit *)
    | "(" whitespace* ")" { UNIT }

    (* integers *)
    | num as n { INT (int_of_string n) }
    
    (* identifiers *)
    | ident_start ident_char* as id { IDENT id }

    (* whitespace (skip) *)
    | whitespace+ { tokenize lexbuf }

    (* end of file *)
    | eof { EOF }

    (* anything unexpected *)
    | _ as c { failwith ("unexpected character: " ^ (Char.escaped c)) }
