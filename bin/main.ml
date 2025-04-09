open Interpreter

let fileName = ref ""
  
let () = Arg.parse [] (fun x -> fileName := x) "a valid file path must be provided"
let exp = Parser.parse Lexer.tokenize (Lexing.from_string (Reader.string_of_file !fileName))

let () = print_newline ()
let () = print_string (Exp.string_of_ast exp)
let () = print_newline ()


let () = 
  match Typechecker.infer exp with 
  | None -> print_string "\nNWT\n"
  | Some t -> 
    let () = print_newline () in
    let () = print_string (Type.string_of_ty t) in
    let () = print_newline () in

    let exp' = Opt.constProp exp in
    let () = print_newline () in
    let () = print_string (Exp.string_of_ast exp') in 
    let () = print_newline () in

    let value = Eval.eval exp' in 
    let () = print_newline () in
    let () = print_string (Exp.string_of_ast value) in 
    let () = print_newline () in
    print_newline ()