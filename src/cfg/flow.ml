open Batteries
open Tezla

type vertex = Adt.stmt Adt.t

type t = {
  nodes : vertex Set.t;
  initial : vertex Set.t;
  final : vertex Set.t;
  flow : (vertex * vertex) Set.t;
}

let rec init n =
  let open Adt in
  match get_node_data n with
  | S_seq (s, _) -> init s
  | S_var_decl _ | S_assign _ | S_skip | S_size | S_empty_set _
  | S_empty_map _ | S_map _ | S_mem | S_get | S_update | S_cast | S_rename
  | S_concat | S_slice | S_pack | S_unpack | S_add | S_sub | S_mul | S_ediv
  | S_abs | S_neg | S_lsl | S_lsr | S_or | S_and | S_xor | S_not | S_compare
  | S_eq | S_neq | S_lt | S_gt | S_le | S_ge | S_self | S_transfer_tokens
  | S_set_delegate | S_create_account | S_implicit_account | S_now | S_amount
  | S_balance | S_check_signature | S_blake2b | S_sha256 | S_sha512
  | S_hash_key | S_steps_to_quota | S_source | S_sender | S_address | S_todo
  | S_exec | S_failwith _ | S_contract _ ->
      n
  | S_create_contract _ | S_dip _ | S_iter _ | S_loop _ | S_loop_left _
  | S_lambda (_, _, _) ->
      n
  | S_if _ | S_while _ | S_if_cons _ -> n

(* TODO: *)

let final x =
  let open Set.Infix in
  let open Adt in
  let rec final_rec acc n =
    match get_node_data n with
    | S_if (_, x, y) | S_if_cons (x, y) -> final_rec (final_rec acc x) y
    | S_seq (_, x) -> final_rec acc x
    | _ -> acc <-- n
  in
  final_rec Set.empty x

let rev_pair x y = (y, x)

let flow x =
  let open Adt in
  let open Set.Infix in
  let ht = Hashtbl.create 10 in
  let rec flow_rec (nodes, flow) n =
    match get_node_data n with
    | S_if (_, x, y) | S_if_cons (x, y) ->
        let flow' = flow <-- (n, init x) <-- (n, init y) in
        flow_rec (flow_rec (nodes, flow') x) y
    | S_while (_, b) ->
        let flow' = Set.map (rev_pair n) (final b) <-- (n, init b) ||. flow in
        flow_rec (nodes, flow') b
    | S_seq (s_1, s_2) ->
        let init_s2 = init s_2 in
        let final_s1 = final s_1 in
        let flow' = flow ||. Set.map (rev_pair init_s2) final_s1 in
        flow_rec (flow_rec (nodes, flow') s_1) s_2
    | _ -> (nodes, flow)
  in
  let nodes', flow = flow_rec (Set.empty, Set.empty) x in
  let initial = Hashtbl.find ht (init x) |> Set.singleton in
  let final = Set.map (Hashtbl.find ht) (final x) in
  let nodes = Set.map (Hashtbl.find ht) nodes' in
  let flow =
    Set.map (fun (a, b) -> (Hashtbl.find ht a, Hashtbl.find ht b)) flow
  in
  { initial; final; nodes; flow }

let flowR n =
  let f = flow n in
  let flow = Set.map (fun (a, b) -> (b, a)) f.flow in
  { f with initial = f.final; final = f.initial; flow }
