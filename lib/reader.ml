(* reader.ml *)
(* Author: Dang Truong, Tran Ong *)

(*
 * string_of_file : string -> string
 * REQUIRES: [filename] is the path to a valid, readable file.
 * ENSURES: Returns the full contents of the file as a string.
 *          Raises Sys_error if the file cannot be opened or read.
 *)
let string_of_file file =
  In_channel.with_open_bin file In_channel.input_all