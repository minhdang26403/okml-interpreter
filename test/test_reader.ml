(* test/test_reader.ml *)
let () =
  let content = Interpreter.Reader.string_of_file "test/example.txt" in
  print_string content
