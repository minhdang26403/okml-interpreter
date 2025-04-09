
{
    open Parser
}

let digit = ['0'-'9']
let nat = digit +
let num = nat | ('-' nat)
let whitespace = (' ' | '\t' | '\n' | '\r')

rule tokenize = parse
    | "+" { PLUS }
    | "*" { TIMES }
    | "(" { LPAREN }
    | ")" { RPAREN }
    | num { INT (lexbuf |> Lexing.lexeme |> int_of_string) }
    | whitespace { tokenize lexbuf } 
    | eof { EOF }
    | _ as c { failwith ("unexpected character: " ^ (Char.escaped c)) }
