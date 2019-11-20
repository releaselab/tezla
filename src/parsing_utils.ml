open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error filename =
  let open Michelson in
  let lexbuf = Lexing.from_channel (open_in filename) in
  try Parser.start Lexer.next_token lexbuf with
  | Lexer.Lexing_error msg as e ->
      Printf.fprintf stderr "%a: %s\n" print_position lexbuf msg;
      raise e
  | Parser.Error as e ->
      Printf.fprintf stderr "%s%a: syntax error\n" filename print_position
        lexbuf;
      raise e

let parse filename =
  let open Michelson in
  Parser.start Lexer.next_token (Lexing.from_channel (open_in filename))
