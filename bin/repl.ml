open Interpreter

let read_input () =
  print_string "OKml> ";
  flush stdout;
  match read_line () with
  | exception End_of_file ->
      print_endline "\nExiting OKml REPL.";
      exit 0
  | line ->
      let trimmed = String.trim line in
      if trimmed = ":q" then (
        print_endline "Exiting OKml REPL.";
        exit 0)
      else if trimmed = "" then ""
      else trimmed

let rec repl () =
  let input = read_input () in
  if input <> "" then (
    let lexbuf = Lexing.from_string input in
    try
      let ast = Parser.parse Lexer.tokenize lexbuf in
      print_endline ("AST: " ^ Exp.string_of_ast ast);
      match Typechecker.infer ast with
      | None ->
          print_endline "Type error: No valid type could be inferred";
          repl ()
      | Some ty ->
          print_endline ("Type: " ^ Type.string_of_ty ty);
          let optimized = Opt.constProp ast in
          print_endline ("Optimized AST: " ^ Exp.string_of_ast optimized);
          let value = Eval.eval optimized in
          print_endline ("Value: " ^ Exp.string_of_ast value);
          print_newline ()
    with
    | Parsing.Parse_error ->
        let pos = lexbuf.lex_curr_p in
        Printf.printf "Parse error at line %d, column %d: near '%s'\n"
          pos.pos_lnum
          (pos.pos_cnum - pos.pos_bol)
          input;
        repl ()
    | Failure msg ->
        print_endline ("Error: " ^ msg);
        repl ()
    | Invalid_argument msg ->
        print_endline ("Error: " ^ msg);
        repl ()
    | e ->
        print_endline ("Unexpected error: " ^ Printexc.to_string e);
        repl ());
  repl ()

let () = repl ()
