open Tezla

let file = Sys.argv.(1)

let () =
  try
    let adt = Parsing_utils.parse_with_error file in
    let p = Converter.convert_program adt in
    Pp.stmt 1 Format.std_formatter p
  with _ -> ()
