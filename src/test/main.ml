open Tezla

let path = Sys.argv.(1)

let () =
  try
    let adt = Parsing_utils.parse_with_error (path ^ "empty.tz") in
    let _ = Converter.convert_program adt in
    Printf.printf "Test empty: OK\n"
  with _ -> Printf.printf "Test empty: not OK\n"

let () =
  try
    let adt = Parsing_utils.parse_with_error (path ^ "empty_code.tz") in
    let _ = Converter.convert_program adt in
    Printf.printf "Test empty_code: OK\n"
  with _ -> Printf.printf "Test empty_code: not OK\n"

let () =
  try
    let adt = Parsing_utils.parse_with_error (path ^ "loop_left.tz") in
    let _ = Converter.convert_program adt in
    Printf.printf "Test loop_left: OK\n"
  with _ -> Printf.printf "Test loop_left: not OK\n"

let () =
  try
    let adt = Parsing_utils.parse_with_error (path ^ "map.tz") in
    let _ = Converter.convert_program adt in
    Printf.printf "Test map: OK\n"
  with _ -> Printf.printf "Test map: not OK\n"

let tests = [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9 ]

let () =
  List.iter
    (fun i ->
      try
        let adt =
          Parsing_utils.parse_with_error
            (path ^ "test" ^ string_of_int i ^ ".tz")
        in
        let _ = Converter.convert_program adt in
        Printf.printf "Test %d: OK\n" i
      with _ as e ->
        Printf.printf "Test %d: not OK | %s\n" i (Printexc.to_string e))
    tests

let () =
  try
    let adt = Parsing_utils.parse_with_error (path ^ "loop_left.tz") in
    let p = Converter.convert_program adt in
    Pp.stmt 1 Format.std_formatter p
  with _ -> ()
