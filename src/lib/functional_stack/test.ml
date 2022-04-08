open Functional_stack

let test_push =
  QCheck.(Test.make ~count:1000 (list int) (fun l -> push 5 l = 5 :: l))

let test_pop =
  QCheck.(
    Test.make ~count:1000 (list int) (fun l ->
        assume (l <> []);
        let h, l' = pop l in
        l = h :: l'))

let test_drop =
  QCheck.(
    Test.make ~count:1000 (list int) (fun l ->
        assume (l <> []);
        let l' = drop l in
        l' = List.tl l))

let test_peek =
  QCheck.(
    Test.make ~count:1000 (list int) (fun l ->
        assume (l <> []);
        let l' = peek l in
        l' = List.hd l))

let test_swap =
  QCheck.(
    Test.make ~count:1000 (list int) (fun l ->
        assume (List.length l > 2);
        let l' = swap l in
        l' = List.hd (List.tl l) :: List.hd l :: List.tl (List.tl l)))

let () =
  exit
    (QCheck_runner.run_tests
       [ test_push; test_pop; test_drop; test_peek; test_swap ])
