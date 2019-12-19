module M = Map.Make (String)
module S = Functional_stack

type abstract_pos = Z.t

type env = Failed | Stack of string Functional_stack.t * abstract_pos M.t

let empty_env = Stack (S.empty, M.empty)

let failed_env = Failed

let var_counter = ref Z.minus_one

let next_var () =
  let () = var_counter := Z.(!var_counter + one) in
  Printf.sprintf "v%s" (Z.to_string !var_counter)

let pos_counter = ref Z.minus_one

let next_pos () =
  let () = pos_counter := Z.(!pos_counter + one) in
  !pos_counter

let add_to_map x = M.add x (next_pos ())

exception Stack_failed

let stack_or_failed = function
  | Failed -> raise Stack_failed
  | Stack (s, m) -> (s, m)

let nth n env =
  let s, m = stack_or_failed env in
  S.find (fun v -> M.find v m = n) s

let push x env =
  let s, m = stack_or_failed env in
  Stack (S.push x s, add_to_map x m)

let pop env =
  let s, m = stack_or_failed env in
  let x, s' = S.pop s in
  let m' = M.remove x m in
  (x, Stack (s', m'))

let drop env =
  let s, m = stack_or_failed env in
  let x, s' = S.pop s in
  let m' = M.remove x m in
  Stack (s', m')

let peek env =
  let s, _ = stack_or_failed env in
  S.peek s

let swap env =
  let s, m = stack_or_failed env in
  Stack (S.swap s, m)

let dig env n =
  let s, m = stack_or_failed env in
  Stack (S.dig s n, m)

let dug env n =
  let s, m = stack_or_failed env in
  Stack (S.dug s n, m)

let dip env n =
  if Z.(n = ~$0) then (empty_env, env)
  else
    let rec aux (acc, env') n' =
      if Z.(n' = ~$0) then (acc, env')
      else
        let x, env'' = pop env' in
        let acc' = push x acc in
        aux (acc', env'') Z.(n' - ~$1)
    in
    aux (empty_env, env) n

let dup env =
  let x = peek env in
  let env' = push x env in
  (x, env')

(* let rename v = function (x, _) :: t -> (x, v) :: t | l -> l *)
