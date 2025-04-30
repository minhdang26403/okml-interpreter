(* reader.ml *)
(* Author: Tran Ong, Dang Truong *)

(*
 * string_of_file : string -> string
 * REQUIRES: [filename] is the path to a valid, readable file.
 * ENSURES: Returns the full contents of the file as a string.
 *          Raises Sys_error if the file cannot be opened or read.
 *)
let string_of_file filename =
  let input_channel = open_in filename in
  let filelen = in_channel_length input_channel in
  let content = really_input_string input_channel filelen in
  close_in input_channel;
  content
