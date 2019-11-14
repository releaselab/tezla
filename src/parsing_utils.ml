open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error filename =
  let open Michelson in
  let lexbuf = Lexing.from_channel (open_in filename) in
  try Some (Parser.start Lexer.next_token lexbuf) with
  | Lexer.Lexing_error msg ->
      Printf.fprintf stderr "%a: %s\n" print_position lexbuf msg;
      None
  | Parser.Error ->
      Printf.fprintf stderr "%s%a: syntax error\n" filename print_position
        lexbuf;
      exit (-1)

let parse filename =
  let open Michelson in
  Parser.start Lexer.next_token (Lexing.from_channel (open_in filename))

let compile filename =
  match parse_with_error filename with
  | Some p -> p
  | None ->
      print_endline "error";
      exit 1
