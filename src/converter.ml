open Env

let join_envs s_t env_t s_f env_f =
  let open Adt in
  match (env_t, env_f) with
  | Failed, env | env, Failed -> (S_skip, env, s_t, s_f)
  | Stack env_t, Stack env_f ->
      let find x =
        let r =
          List.fold_left2
            (fun acc v_t v_f ->
              match acc with
              | Some _ as acc -> acc
              | None -> if v_t = x then Some v_f else None)
            None env_t env_f
        in
        Option.get r
      in
      let s_t' =
        match s_t with S_assign (v, e, t) -> S_assign (find v, e, t) | s -> s
      in
      let decls =
        List.fold_left (fun acc v -> S_seq (acc, S_var_decl v)) S_skip env_f
      in
      (decls, Stack env_f, s_t', s_f)

let join_envs_while s env =
  let decls, env, s, _ = join_envs s env s env in
  (decls, env, s)

(* let open Adt in
  let env' = join env env in
  let decls =
    match env' with
    | Failed -> S_skip
    | Stack env'' ->
        List.fold_left (fun acc v -> S_seq (acc, S_var_decl v)) S_skip env''
  in
  let assigns =
    match (env, env') with
    | Failed, _ | _, Failed -> S_skip
    | Stack env, Stack env' ->
        List.fold_left2
          (fun acc x v -> S_seq (acc, S_assign (v, E_ident x, None)))
          S_skip env env'
  in
  let s' = S_seq (decls, S_seq (s, assigns)) in
  (env', s') *)

let rec data_to_expr =
  let open Michelson.Adt in
  let open Adt in
  function
  | D_int i -> E_int i
  | D_nat i -> E_nat i
  | D_string s -> E_string s
  | D_timestamp s -> E_timestamp s
  | D_signature s -> E_signature s
  | D_key s -> E_key s
  | D_key_hash s -> E_key_hash s
  | D_mutez s -> E_mutez s
  | D_unit -> E_unit
  | D_bool x -> E_bool x
  | D_pair (x, y) -> E_pair (data_to_expr x, data_to_expr y)
  | D_left x -> E_left (data_to_expr x)
  | D_right x -> E_right (data_to_expr x)
  | D_some x -> E_some (data_to_expr x)
  | D_none t -> E_none t
  | D_list (t, x) -> E_list (t, List.map (fun e -> data_to_expr e) x)
  | D_set (_, x) -> E_set (List.map (fun e -> data_to_expr e) x)
  | D_map x ->
      E_map (List.map (fun (x, y) -> (data_to_expr x, data_to_expr y)) x)
  | D_bytes x -> E_bytes x
  | D_address x -> E_address_of_contract (E_ident x)

(* | D_instruction x ->
        let s, _ = convert empty_env x in
        E_stmt s *)
and convert env (i, a) =
  let open Michelson.Adt in
  let open Adt in
  let loop_n f =
    let rec loop acc n =
      if Z.(n = zero) then acc else loop (f acc n) Z.(n - one)
    in
    loop
  in
  let create_assign ?t e =
    let v = next_var () in
    (v, S_assign (v, e, t))
  in
  match i with
  | I_push (t, x) ->
      let e = data_to_expr x in
      let v, assign = create_assign ~t e in
      (assign, push v env)
  | I_seq (i_1, i_2) ->
      let s_1, env_1 = convert env i_1 in
      let s_2, env_2 = convert env_1 i_2 in
      (S_seq (s_1, s_2), env_2)
  | I_drop ->
      let x, env' = pop env in
      (S_drop x, env')
  | I_drop_n n ->
      let s, env' =
        loop_n
          (fun (s, env) _ ->
            let x, env' = pop env in
            (S_seq (s, S_drop x), env'))
          (S_skip, env) n
      in
      (s, env')
  | I_dup ->
      let x = peek env in
      let v, assign = create_assign (E_ident x) in
      (assign, push v env)
  | I_dig n -> (S_skip, dig env n)
  | I_dug n -> (S_skip, dug env n)
  | I_swap ->
      let env' = swap env in
      (S_skip, env')
  | I_some ->
      let x, env' = pop env in
      let v, assign = create_assign (E_some (E_ident x)) in
      (assign, push v env')
  | I_none t ->
      let v, assign = create_assign (E_none t) in
      (assign, push v env)
  | I_unit ->
      let v, assign = create_assign E_unit in
      (assign, push v env)
  | I_if_none (i_t, i_f) ->
      let x, env' = pop env in
      let s_t, env_t = convert env' i_t in
      let v, assign = create_assign (E_lift_option (E_ident x)) in
      let s_f, env_f = convert (push v env') i_f in
      let decls, env', s_t', s_f' = join_envs s_t env_t s_f env_f in
      let s_f' = S_seq (assign, s_f') in
      (S_seq (decls, S_if_none (x, s_t', s_f', v)), env')
  | I_pair ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_pair (E_ident x_1, E_ident x_2)) in
      (assign, push v env')
  | I_car ->
      let x, env' = pop env in
      let v, assign = create_assign (E_car (E_ident x)) in
      (assign, push v env')
  | I_cdr ->
      let x, env' = pop env in
      let v, assign = create_assign (E_cdr (E_ident x)) in
      (assign, push v env')
  | I_left _ ->
      let x, env' = pop env in
      let v, assign = create_assign (E_left (E_ident x)) in
      (assign, push v env')
  | I_right _ ->
      let x, env' = pop env in
      let v, assign = create_assign (E_right (E_ident x)) in
      (assign, push v env')
  | I_if_left (i_t, i_f) ->
      let x, env' = pop env in
      let e = E_lift_or (E_ident x) in
      let v, assign = create_assign e in
      let env' = push v env' in
      let s_t, env_t = convert env' i_t in
      let s_f, env_f = convert env' i_f in
      let decls, env', s_t', s_f' = join_envs s_t env_t s_f env_f in
      let s_t' = S_seq (assign, s_t') in
      let s_f' = S_seq (assign, s_f') in
      (S_seq (decls, S_if_left (x, s_t', s_f', v)), env')
  | I_if_right (i_t, i_f) -> convert env (I_if_left (i_f, i_t), a)
  | I_nil t ->
      let v, assign = create_assign (E_list (t, [])) in
      (assign, push v env)
  | I_cons ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_cons (E_ident x_1, E_ident x_2)) in
      (assign, push v env')
  | I_if_cons (i_t, i_f) ->
      let x, env_f = pop env in
      let hd = E_list_hd (E_ident x) in
      let tl = E_list_tl (E_ident x) in
      let v_hd, assign_hd = create_assign hd in
      let v_tl, assign_tl = create_assign tl in
      let env_t = push v_hd (push v_tl env_f) in
      let s_t, env_t' = convert env_t i_t in
      let s_f, env_f' = convert env_f i_f in
      let decls, env', s_t', s_f' = join_envs s_t env_t' s_f env_f' in
      let s_t' = S_seq (assign_hd, S_seq (assign_tl, s_t')) in
      (S_seq (decls, S_if_cons (x, s_t', v_hd, v_tl, s_f')), env')
  | I_size ->
      let x, env' = pop env in
      let v, assign = create_assign (E_size (E_ident x)) in
      (assign, push v env')
  | I_empty_set _ ->
      let v, assign = create_assign (E_set []) in
      (assign, push v env)
  | I_empty_map _ ->
      let v, assign = create_assign (E_map []) in
      (assign, push v env)
  | I_empty_big_map _ ->
      let v, assign = create_assign (E_big_map []) in
      (assign, push v env)
  | I_map b ->
      let body, _ = convert empty_env b in
      let x, env' = pop env in
      (S_map (x, body), env')
  | I_iter b ->
      let x, env' = pop env in
      let v, assign = create_assign (E_list_hd (E_ident x)) in
      let assign' = S_assign (x, E_list_tl (E_ident x), None) in
      let body, env' = convert (push v env') b in
      let body = S_seq (assign, S_seq (body, assign')) in
      (S_iter (x, body), env')
  | I_mem ->
      let elt, env' = pop env in
      let set, env' = pop env' in
      let v, assign = create_assign (E_mem (E_ident elt, E_ident set)) in
      (assign, push v env')
  | I_get ->
      let key, env' = pop env in
      let map, env' = pop env' in
      let v, assign = create_assign (E_get (E_ident key, E_ident map)) in
      (assign, push v env')
  | I_update ->
      let key, env' = pop env in
      let value, env' = pop env' in
      let map, env' = pop env' in
      let v, assign =
        create_assign (E_update (E_ident key, E_ident value, E_ident map))
      in
      (assign, push v env')
  | I_if (i_t, i_f) ->
      let c, env' = pop env in
      let s_t, env_t' = convert env' i_t in
      let s_f, env_f' = convert env' i_f in
      let decls, env', s_t', s_f' = join_envs s_t env_t' s_f env_f' in
      (S_seq (decls, S_if (c, s_t', s_f')), env')
  | I_loop i ->
      let c, env' = pop env in
      let s, env' = convert env' i in
      let decls, env', s' = join_envs_while s (drop env') in
      (S_seq (decls, S_loop (c, s')), env')
  | I_loop_left i ->
      let x, env' = pop env in
      let e = E_lift_or (E_ident x) in
      let v, assign = create_assign e in
      let s, env' = convert (push v env') i in
      let decls, env', s' = join_envs_while s env' in
      let x', env' = pop env' in
      let v', assign' = create_assign (E_lift_or (E_ident x')) in
      let env' = push v' env' in
      let s' = S_seq (assign, s') in
      (S_seq (decls, S_seq (S_loop_left (x, s'), assign')), env')
  | I_lambda (t_1, t_2, i) ->
      let b, lambda_env = convert (push "param" empty_env) i in
      let r, _ = pop lambda_env in
      let v, assign = create_assign (E_lambda (t_1, t_2, (b, r))) in
      (assign, push v env)
  | I_exec ->
      let param, env' = pop env in
      let lambda, env' = pop env' in
      let v, assign = create_assign (E_exec (lambda, param)) in
      (assign, push v env')
  | I_dip i ->
      let x, env' = pop env in
      let s, env' = convert env' i in
      (s, push x env')
  | I_dip_n (n, i) ->
      let xl, env' = dip env n in
      let s, env' = convert env' i in
      let env' = List.fold_left (fun acc x -> push x acc) env' xl in
      (s, env')
  | I_failwith ->
      let x, _ = pop env in
      (S_failwith x, Failed)
  | I_cast -> (S_skip, env)
  | I_rename -> (S_skip, env)
  | I_concat ->
      let s, env' = pop env in
      let t, env' = pop env' in
      let v, assign = create_assign (E_concat (E_ident s, E_ident t)) in
      (assign, push v env')
  | I_slice ->
      let offset, env' = pop env in
      let length, env' = pop env' in
      let x, env' = pop env' in
      let v, assign =
        create_assign (E_slice (E_ident offset, E_ident length, E_ident x))
      in
      (assign, push v env')
  | I_pack ->
      let x, env' = pop env in
      let v, assign = create_assign (E_pack (E_ident x)) in
      (assign, push v env')
  | I_unpack t ->
      let x, env' = pop env in
      let v, assign = create_assign (E_unpack (t, E_ident x)) in
      (assign, push v env')
  | I_add ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_add (E_ident x_1, E_ident x_2)) in
      (assign, push v env')
  | I_sub ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_sub (E_ident x_1, E_ident x_2)) in
      (assign, push v env')
  | I_mul ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_mul (E_ident x_1, E_ident x_2)) in
      (assign, push v env')
  | I_ediv ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_div (E_ident x_1, E_ident x_2)) in
      (assign, push v env')
  | I_abs ->
      let x, env' = pop env in
      let v, assign = create_assign (E_abs (E_ident x)) in
      (assign, push v env')
  | I_neg ->
      let x, env' = pop env in
      let v, assign = create_assign (E_neg (E_ident x)) in
      (assign, push v env')
  | I_lsl ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_shiftL (E_ident x_1, E_ident x_2)) in
      (assign, push v env')
  | I_lsr ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_shiftR (E_ident x_1, E_ident x_2)) in
      (assign, push v env')
  | I_or ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_or (E_ident x_1, E_ident x_2)) in
      (assign, push v env')
  | I_and ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_and (E_ident x_1, E_ident x_2)) in
      (assign, push v env')
  | I_xor ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_xor (E_ident x_1, E_ident x_2)) in
      (assign, push v env')
  | I_not ->
      let x, env' = pop env in
      let v, assign = create_assign (E_not (E_ident x)) in
      (assign, push v env')
  | I_compare ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_compare (E_ident x_1, E_ident x_2)) in
      (assign, push v env')
  | I_eq ->
      let x, env' = pop env in
      let v, assign = create_assign (E_eq (E_ident x)) in
      (assign, push v env')
  | I_neq ->
      let x, env' = pop env in
      let v, assign = create_assign (E_neq (E_ident x)) in
      (assign, push v env')
  | I_lt ->
      let x, env' = pop env in
      let v, assign = create_assign (E_lt (E_ident x)) in
      (assign, push v env')
  | I_gt ->
      let x, env' = pop env in
      let v, assign = create_assign (E_gt (E_ident x)) in
      (assign, push v env')
  | I_le ->
      let x, env' = pop env in
      let v, assign = create_assign (E_leq (E_ident x)) in
      (assign, push v env')
  | I_ge ->
      let x, env' = pop env in
      let v, assign = create_assign (E_geq (E_ident x)) in
      (assign, push v env')
  | I_self ->
      let v, assign = create_assign E_self in
      (assign, push v env)
  | I_contract _ ->
      let x, env' = pop env in
      let v, assign = create_assign (E_contract_of_address (E_ident x)) in
      (assign, push v env')
  | I_transfer_tokens ->
      let x, env' = pop env in
      let amount, env' = pop env' in
      let contract, env' = pop env' in
      let operation =
        O_transfer_tokens (E_ident x, E_ident amount, E_ident contract)
      in
      let v, assign = create_assign (E_operation operation) in
      (assign, push v env')
  | I_set_delegate ->
      let x, env' = pop env in
      let o = O_set_delegate (E_ident x) in
      let v, assign = create_assign (E_operation o) in
      (assign, push v env')
  | I_create_account ->
      let manager, env' = pop env in
      let delegate, env' = pop env' in
      let delegatable, env' = pop env' in
      let amount, env' = pop env' in
      let o =
        O_create_account
          ( E_ident manager,
            E_ident delegate,
            E_ident delegatable,
            E_ident amount )
      in
      let v_o, assign_o = create_assign (E_operation o) in
      let v_a, assign_a = create_assign (E_create_account_address o) in
      (S_seq (assign_o, assign_a), push v_o (push v_a env'))
  | I_create_contract c ->
      let delegate, env' = pop env in
      let amount, env' = pop env' in
      let storage, env' = pop env' in
      let o =
        O_create_contract (c, E_ident delegate, E_ident amount, E_ident storage)
      in
      let v_o, assign_o = create_assign (E_operation o) in
      let v_a, assign_a = create_assign (E_create_account_address o) in
      let env' = push v_o (push v_a env') in
      (S_seq (assign_o, assign_a), env')
  | I_implicit_account ->
      let x, env' = pop env in
      let v, assign = create_assign (E_implicit_account (E_ident x)) in
      (assign, push v env')
  | I_now ->
      let v, assign = create_assign E_now in
      (assign, push v env)
  | I_amount ->
      let v, assign = create_assign E_amount in
      (assign, push v env)
  | I_balance ->
      let v, assign = create_assign E_balance in
      (assign, push v env)
  | I_check_signature ->
      let key, env' = pop env in
      let signature, env' = pop env' in
      let bytes, env' = pop env' in
      let v, assign =
        create_assign
          (E_check_signature (E_ident key, E_ident signature, E_ident bytes))
      in
      (assign, push v env')
  | I_blake2b ->
      let x, env' = pop env in
      let v, assign = create_assign (E_blake2b (E_ident x)) in
      (assign, push v env')
  | I_sha256 ->
      let x, env' = pop env in
      let v, assign = create_assign (E_sha256 (E_ident x)) in
      (assign, push v env')
  | I_sha512 ->
      let x, env' = pop env in
      let v, assign = create_assign (E_sha512 (E_ident x)) in
      (assign, push v env')
  | I_hash_key ->
      let x, env' = pop env in
      let v, assign = create_assign (E_hash_key (E_ident x)) in
      (assign, push v env')
  | I_steps_to_quota ->
      let v, assign = create_assign E_steps_to_quota in
      (assign, push v env)
  | I_source ->
      let v, assign = create_assign E_source in
      (assign, push v env)
  | I_sender ->
      let v, assign = create_assign E_sender in
      (assign, push v env)
  | I_address ->
      let x, env' = pop env in
      let v, assign = create_assign (E_address_of_contract (E_ident x)) in
      (assign, push v env')
  | I_isnat ->
      let x, env' = pop env in
      let v, assign = create_assign (E_isnat (E_ident x)) in
      (assign, push v env')
  | I_int ->
      let x, env' = pop env in
      let v, assign =
        create_assign (E_address_of_contract (E_int_of_nat (E_ident x)))
      in
      (assign, push v env')
  | I_chain_id ->
      let v, assign = create_assign E_chain_id in
      (assign, push v env)
  | I_noop -> (S_skip, env)

let convert_program p =
  let env = Env.push (next_var ()) Env.empty_env in
  fst (convert env (p.Michelson.Adt.code, []))

(* | _ -> assert false *)
