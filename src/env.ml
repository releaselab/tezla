type 'a env = 'a list

let empty_env = []

let var_counter = ref (-1)

let next_var () =
  let () = var_counter := !var_counter + 1 in
  Printf.sprintf "v%d" !var_counter

(* let push ?name x =
  let v = match name with None -> next_var () | Some s -> s in
  List.cons (x, v) *)
let push = List.cons

let pop env = (List.hd env, List.tl env)

let drop = List.tl

let peek = List.hd

let swap = function h :: h' :: t -> h' :: h :: t | l -> l

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
    fst (aux ([], env) n)

let dug env n =
  if Z.(n = ~$0) then env
  else if Z.(n = ~$1) then swap env
  else
    match env with
    | [] -> env
    | top :: t ->
        let rec aux (l_h, l_t) n' =
          match l_t with
          | [] -> (top :: l_t, [])
          | _ when Z.(n' = ~$0) -> (l_h @ (top :: l_t), [])
          | h :: t -> aux (l_h @ [ h ], t) Z.(n' - ~$1)
        in
        fst (aux ([], t) n)

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

let join string_to_expr env_1 =
  List.map2 (fun _ _ -> string_to_expr (next_var ())) env_1
