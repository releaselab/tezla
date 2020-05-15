open Tezla

(* 
let path =
  let doc = "Directory where the test files are located." in
  Cmdliner.Arg.(
    required & opt (some string) None & info [ "d" ] ~doc ~docv:"DIR")

let tests path =
  let template file path =
    try
      let adt = Parsing_utils.parse_with_error (path ^ file) in
      let _ = Converter.convert_program (ref (-1)) adt in
      Printf.printf "Test %s: OK\n" file
    with e ->
      let msg = Printexc.to_string e in
      let stack = Printexc.get_backtrace () in
      Alcotest.failf "Test %s: not OK | %s%s\n" file msg stack
  in
  let dir_files = Sys.readdir path in
  Array.map (fun file -> (file, `Quick, template file)) dir_files
  |> Array.to_list

let test_empty path =
  try
    let adt = Parsing_utils.parse_with_error (path ^ "empty.tz") in
    let _ = Converter.convert_program (ref (-1)) adt in
    Printf.printf "Test empty: OK\n"
  with _ -> Printf.printf "Test empty: not OK\n"

let test_empty_code path =
  try
    let adt = Parsing_utils.parse_with_error (path ^ "empty_code.tz") in
    let _ = Converter.convert_program (ref (-1)) adt in
    Printf.printf "Test empty_code: OK\n"
  with _ -> Printf.printf "Test empty_code: not OK\n"

let test_loop_left path =
  try
    let adt = Parsing_utils.parse_with_error (path ^ "loop_left.tz") in
    let _ = Converter.convert_program (ref (-1)) adt in
    Printf.printf "Test loop_left: OK\n"
  with _ -> Printf.printf "Test loop_left: not OK\n"

let test_map path =
  try
    let adt = Parsing_utils.parse_with_error (path ^ "map.tz") in
    let _ = Converter.convert_program (ref (-1)) adt in
    Printf.printf "Test map: OK\n"
  with _ -> Printf.printf "Test map: not OK\n"

let test_i path =
  let tests = [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9 ] in
  List.iter
    (fun i ->
      try
        let adt =
          Parsing_utils.parse_with_error
            (path ^ "test" ^ string_of_int i ^ ".tz")
        in
        let _ = Converter.convert_program (ref (-1)) adt in
        Printf.printf "Test %d: OK\n" i
      with _ as e ->
        Printf.printf "Test %d: not OK\n%s" i (Printexc.to_string e);
        Printexc.print_backtrace stdout)
    tests

let () =
  let open Alcotest in
  run_with_args "Tezla" path
    [
      ( "convert",
        [
          ("empty", `Quick, test_empty);
          ("empty code", `Quick, test_empty_code);
          ("i", `Quick, test_i);
          ("loop left", `Quick, test_loop_left);
          ("map", `Quick, test_map);
        ] );
    ] *)

let path = Sys.argv.(1)

let () =
  let template file =
    try
      let adt = Parsing_utils.parse_with_error (path ^ file) in
      let _ = Converter.convert_program (ref (-1)) adt in
      Printf.printf "Test %s: OK\n" file
    with e ->
      let msg = Printexc.to_string e in
      let stack = Printexc.get_backtrace () in
      Printf.eprintf "Test %s: not OK | %s%s\n" file msg stack
  in
  let dir_files = Sys.readdir path in
  Array.iter template dir_files
