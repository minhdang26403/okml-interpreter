(* repl.ml *)
open Interpreter

let rec repl () =
  print_string "OKml> ";
  flush stdout;
  match read_line () with
  | exception End_of_file -> print_endline "\nExiting OKml REPL."; exit 0
  | line ->
    let lexbuf = Lexing.from_string line in
    try
      let ast = Parser.parse Lexer.tokenize lexbuf in
      print_endline ("AST: " ^ Exp.string_of_ast ast);
      repl ()
    with
    | Parsing.Parse_error ->
      let pos = lexbuf.lex_curr_p in
      Printf.printf "Parse error at line %d, column %d\n%!"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol);
      repl ()

let () = repl ()