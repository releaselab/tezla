let () =
  let dir = "../../../../tests/" in
  let files = Sys.readdir dir in
  let open Alcotest in
  let create_test file =
    let open Michelson.Parser in
    let parse_f () =
      let adt = parse_file (dir ^ file) in
      let adt = convert adt in
      let _ = Tezla.Converter.convert_program (ref (-1)) adt in
      ()
    in
    let test_f () =
      try
        parse_f ();
        check pass "Ok" () ()
      with Failure s -> fail ("Parsing error: " ^ s)
    in
    test_case file `Quick test_f
  in
  let tests = Array.map create_test files in
  let tests = Array.to_list tests in
  run "Michelson parser" [ ("parsing", tests) ]