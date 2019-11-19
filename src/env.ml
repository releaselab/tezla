type 'a env = Failed | Stack of 'a list

let empty_env = Stack []

let var_counter = ref (-1)

let next_var () =
  let () = var_counter := !var_counter + 1 in
  Printf.sprintf "v%d" !var_counter

(* let push ?name x =
  let v = match name with None -> next_var () | Some s -> s in
  List.cons (x, v) *)

exception Stack_failed

let stack_or_failed = function Failed -> raise Stack_failed | Stack s -> s

let push x env = Stack (List.cons x (stack_or_failed env))

let pop env =
  let env' = stack_or_failed env in
  (List.hd env', Stack (List.tl env'))

let drop env = Stack (List.tl (stack_or_failed env))

let peek env = List.hd (stack_or_failed env)

let swap env =
  match stack_or_failed env with
  | h :: h' :: t -> Stack (h' :: h :: t)
  | l -> Stack l

let dig env n =
  if Z.(n = ~$0) then env
  else if Z.(n = ~$1) then swap env
  else
    let rec aux (l_h, l_t) n =
      match l_t with
      | h :: t when Z.(n = ~$0) -> ((h :: l_h) @ t, [])
      | h :: t -> aux (l_h @ [ h ], t) Z.(n - one)
      | [] -> ([], [])
    in
    Stack (fst (aux ([], stack_or_failed env) n))

let dug env n =
  if Z.(n = ~$0) then env
  else if Z.(n = ~$1) then swap env
  else
    match stack_or_failed env with
    | [] -> env
    | top :: t ->
        let rec aux (l_h, l_t) n' =
          match l_t with
          | [] -> (top :: l_t, [])
          | _ when Z.(n' = ~$0) -> (l_h @ (top :: l_t), [])
          | h :: t -> aux (l_h @ [ h ], t) Z.(n' - ~$1)
        in
        Stack (fst (aux ([], t) n))

let dip env n =
  if Z.(n = ~$0) then ([], env)
  else
    let rec aux (acc, env') n' =
      if Z.(n' = ~$0) then (acc, env')
      else
        let x, env'' = pop env' in
        aux (x :: acc, env'') Z.(n' - ~$1)
    in
    aux ([], env) n

(* let rename v = function (x, _) :: t -> (x, v) :: t | l -> l *)

let join string_to_expr env_1 env_2 =
  match (env_1, env_2) with
  | Failed, Failed -> Failed
  | Failed, Stack env | Stack env, Failed ->
      Stack (List.map (fun _ -> string_to_expr (next_var ())) env)
  | Stack env_1', Stack env_2' ->
      Stack (List.map2 (fun _ _ -> string_to_expr (next_var ())) env_1' env_2')
