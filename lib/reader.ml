(* reader.ml *)
(* Author: Dang Truong, Tran Ong *)

let string_of_file (file : string) : string =
  In_channel.with_open_bin file In_channel.input_all