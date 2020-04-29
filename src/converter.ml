open Env

let join counter env_t env_f =
  let open Adt in
  match (env_t, env_f) with
  | Failed, env | env, Failed -> (env, create_stmt S_skip)
  | Stack env_t, Stack env_f ->
      let env_after =
        List.map2 (fun v f -> if v = f then v else next_var counter) env_t env_f
      in
      let rec phi acc env_after env_t env_f =
        match (env_after, env_t, env_f) with
        | [], [], [] -> acc
        | after :: env_after, t :: env_t, f :: env_f when t <> f ->
            let s = create_stmt (S_assign (after, E_phi (t, f))) in
            phi (create_stmt (S_seq (s, acc))) env_after env_t env_f
        | _ :: env_after, _ :: env_t, _ :: env_f ->
            phi acc env_after env_t env_f
        | _ -> assert false
      in
      let phis =
        phi (create_stmt S_skip) (List.rev env_after) (List.rev env_t)
          (List.rev env_f)
      in
      (Stack env_after, phis)

let rec inst_to_stmt counter env (i, a) =
  let open Michelson.Adt in
  let open Adt in
  let loop_n f =
    let rec loop acc n =
      if Z.(n = zero) then acc else loop (f acc n) Z.(n - one)
    in
    loop
  in
  let next_var () = next_var counter in
  let create_assign e =
    let v = next_var () in
    (v, create_stmt (S_assign (v, e)))
  in
  match i with
  | I_push (t, x) ->
      let e = E_push (x, t) in
      let v, assign = create_assign e in
      (assign, push v env)
  | I_seq (i_1, i_2) ->
      let s_1, env_1 = inst_to_stmt counter env i_1 in
      let s_2, env_2 = inst_to_stmt counter env_1 i_2 in
      (create_stmt (S_seq (s_1, s_2)), env_2)
  | I_drop ->
      let x, env' = pop env in
      (create_stmt (S_drop [ x ]), env')
  | I_drop_n n ->
      let env', l =
        loop_n
          (fun (env, l) _ ->
            let x, env = pop env in
            (env, x :: l))
          (env, []) n
      in
      (create_stmt (S_drop l), env')
  | I_dup ->
      let x = peek env in
      let v, assign = create_assign (E_dup x) in
      (assign, push v env)
  | I_dig n -> (create_stmt S_dig, dig env n)
  | I_dug n -> (create_stmt S_dug, dug env n)
  | I_swap ->
      let env' = swap env in
      (create_stmt S_swap, env')
  | I_some ->
      let x, env' = pop env in
      let v, assign = create_assign (E_some x) in
      (assign, push v env')
  | I_none t ->
      let v, assign = create_assign (E_none t) in
      (assign, push v env)
  | I_unit ->
      let v, assign = create_assign E_unit in
      (assign, push v env)
  | I_if_none (i_t, i_f) ->
      let x, env' = pop env in
      let s_t, env_t = inst_to_stmt counter env' i_t in
      let v, assign = create_assign (E_unlift_option x) in
      let s_f, env_f = inst_to_stmt counter (push v env') i_f in
      let env', phis = join counter env_t env_f in
      let s_f = create_stmt (S_seq (assign, s_f)) in
      let s =
        create_stmt (S_seq (create_stmt (S_if_none (x, s_t, s_f)), phis))
      in
      (s, env')
  | I_pair ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_pair (x_1, x_2)) in
      (assign, push v env')
  | I_car ->
      let x, env' = pop env in
      let v, assign = create_assign (E_car x) in
      (assign, push v env')
  | I_cdr ->
      let x, env' = pop env in
      let v, assign = create_assign (E_cdr x) in
      (assign, push v env')
  | I_left t ->
      let x, env' = pop env in
      let v, assign = create_assign (E_left (x, t)) in
      (assign, push v env')
  | I_right t ->
      let x, env' = pop env in
      let v, assign = create_assign (E_right (x, t)) in
      (assign, push v env')
  | I_if_left (i_t, i_f) ->
      let x, env' = pop env in
      let e = E_unlift_or x in
      let v, assign = create_assign e in
      let env'' = push v env' in
      let s_t, env_t = inst_to_stmt counter env'' i_t in
      let s_f, env_f = inst_to_stmt counter env'' i_f in
      let env', phis = join counter env_t env_f in
      let s_t = create_stmt (S_seq (assign, s_t)) in
      let s_f = create_stmt (S_seq (assign, s_f)) in
      let s =
        create_stmt (S_seq (create_stmt (S_if_left (x, s_t, s_f)), phis))
      in
      (s, env')
  | I_if_right (i_t, i_f) -> inst_to_stmt counter env (I_if_left (i_f, i_t), a)
  | I_nil t ->
      let v, assign = create_assign (E_nil t) in
      (assign, push v env)
  | I_cons ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_cons (x_1, x_2)) in
      (assign, push v env')
  | I_if_cons (i_t, i_f) ->
      let c, env' = pop env in
      let v_hd, assign_hd =
        let e_hd = E_hd c in
        create_assign e_hd
      in
      let v_tl, assign_tl =
        let e_tl = E_tl c in
        create_assign e_tl
      in
      let env_t = push v_hd (push v_tl env') in
      let env_f = env' in
      let s_t, env_t = inst_to_stmt counter env_t i_t in
      let s_f, env_f = inst_to_stmt counter env_f i_f in
      let env', phis = join counter env_t env_f in
      let s_t =
        create_stmt (S_seq (assign_hd, create_stmt (S_seq (assign_tl, s_t))))
      in
      let s =
        create_stmt (S_seq (create_stmt (S_if_cons (c, s_t, s_f)), phis))
      in
      (s, env')
  | I_size ->
      let x, env' = pop env in
      let v, assign = create_assign (E_size x) in
      (assign, push v env')
  | I_empty_set t ->
      let v, assign = create_assign (E_empty_set t) in
      (assign, push v env)
  | I_empty_map (t_k, t_v) ->
      let v, assign = create_assign (E_empty_map (t_k, t_v)) in
      (assign, push v env)
  | I_empty_big_map (t_k, t_v) ->
      let v, assign = create_assign (E_empty_big_map (t_k, t_v)) in
      (assign, push v env)
  | I_map b ->
      let c, env' = pop env in
      let empty_list, empty_list_assign = create_assign E_special_nil_list in
      let loop_var = next_var () in
      let result = next_var () in
      let hd, assign_hd = create_assign (E_hd loop_var) in
      let body, env' =
        let body_env = push hd env' in
        inst_to_stmt counter body_env b
      in
      let tl, assign_tl = create_assign (E_tl loop_var) in
      let x, env' = pop env' in
      let append, assign_append = create_assign (E_append (result, x)) in
      let body =
        create_stmt
          (S_seq
             ( assign_hd,
               create_stmt
                 (S_seq (body, create_stmt (S_seq (assign_append, assign_tl))))
             ))
      in
      let s =
        create_stmt
          (S_seq
             ( empty_list_assign,
               create_stmt
                 (S_map
                    ((loop_var, (c, tl)), (result, (empty_list, append)), body))
             ))
      in
      (s, push result env')
  | I_iter b ->
      let c, env' = pop env in
      let loop_var = next_var () in
      let hd, assign_hd = create_assign (E_hd loop_var) in
      let body, env' =
        let body_env = push hd env' in
        inst_to_stmt counter body_env b
      in
      let tl, assign_tl = create_assign (E_tl loop_var) in
      let body =
        create_stmt (S_seq (assign_hd, create_stmt (S_seq (body, assign_tl))))
      in
      let s = create_stmt (S_iter (loop_var, (c, tl), body)) in
      (s, env')
  | I_mem ->
      let elt, env' = pop env in
      let set, env' = pop env' in
      let v, assign = create_assign (E_mem (elt, set)) in
      (assign, push v env')
  | I_get ->
      let key, env' = pop env in
      let map, env' = pop env' in
      let v, assign = create_assign (E_get (key, map)) in
      (assign, push v env')
  | I_update ->
      let key, env' = pop env in
      let value, env' = pop env' in
      let map, env' = pop env' in
      let v, assign = create_assign (E_update (key, value, map)) in
      (assign, push v env')
  | I_if (i_t, i_f) ->
      let c, env' = pop env in
      let s_t, env_t = inst_to_stmt counter env' i_t in
      let s_f, env_f = inst_to_stmt counter env' i_f in
      let env', phis = join counter env_t env_f in
      let s = create_stmt (S_seq (create_stmt (S_if (c, s_t, s_f)), phis)) in
      (s, env')
  | I_loop i ->
      let c, env' = pop env in
      let loop_var = next_var () in
      let body, env' = inst_to_stmt counter env' i in
      let loop_result, env' = pop env' in
      let s = create_stmt (S_loop (loop_var, (c, loop_result), body)) in
      (s, env')
  | I_loop_left i ->
      let c, env' = pop env in
      let loop_var = next_var () in
      let e = E_unlift_or loop_var in
      let v, assign_unlift = create_assign e in
      let body, env' =
        let body_env = push v env' in
        inst_to_stmt counter body_env i
      in
      let loop_result, env' = pop env' in
      let body = create_stmt (S_seq (assign_unlift, body)) in
      let post_loop_unlift = E_unlift_or loop_var in
      let v_post_loop, post_loop_assign_unlift =
        create_assign post_loop_unlift
      in
      let s =
        create_stmt
          (S_seq
             ( create_stmt (S_loop_left (loop_var, (c, loop_result), body)),
               post_loop_assign_unlift ))
      in
      let env' = push v_post_loop env' in
      (s, env')
  | I_lambda (t_1, t_2, i) ->
      let b, lambda_env = inst_to_stmt counter (push "param" empty_env) i in
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
      let s, env' = inst_to_stmt counter env' i in
      (s, push x env')
  | I_dip_n (n, i) ->
      let xl, env' = dip env n in
      let s, env' = inst_to_stmt counter env' i in
      let env' = List.fold_left (fun acc x -> push x acc) env' xl in
      (s, env')
  | I_failwith ->
      let x, _ = pop env in
      (create_stmt (S_failwith x), Failed)
  | I_cast -> (create_stmt S_skip, env)
  | I_rename -> (create_stmt S_skip, env)
  | I_concat ->
      let s, env' = pop env in
      let t, env' = pop env' in
      let v, assign = create_assign (E_concat (s, t)) in
      (assign, push v env')
  | I_slice ->
      let offset, env' = pop env in
      let length, env' = pop env' in
      let x, env' = pop env' in
      let v, assign = create_assign (E_slice (offset, length, x)) in
      (assign, push v env')
  | I_pack ->
      let x, env' = pop env in
      let v, assign = create_assign (E_pack x) in
      (assign, push v env')
  | I_unpack t ->
      let x, env' = pop env in
      let v, assign = create_assign (E_unpack (t, x)) in
      (assign, push v env')
  | I_add ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_add (x_1, x_2)) in
      (assign, push v env')
  | I_sub ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_sub (x_1, x_2)) in
      (assign, push v env')
  | I_mul ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_mul (x_1, x_2)) in
      (assign, push v env')
  | I_ediv ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_div (x_1, x_2)) in
      (assign, push v env')
  | I_abs ->
      let x, env' = pop env in
      let v, assign = create_assign (E_abs x) in
      (assign, push v env')
  | I_neg ->
      let x, env' = pop env in
      let v, assign = create_assign (E_neg x) in
      (assign, push v env')
  | I_lsl ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_shiftL (x_1, x_2)) in
      (assign, push v env')
  | I_lsr ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_shiftR (x_1, x_2)) in
      (assign, push v env')
  | I_or ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_or (x_1, x_2)) in
      (assign, push v env')
  | I_and ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_and (x_1, x_2)) in
      (assign, push v env')
  | I_xor ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_xor (x_1, x_2)) in
      (assign, push v env')
  | I_not ->
      let x, env' = pop env in
      let v, assign = create_assign (E_not x) in
      (assign, push v env')
  | I_compare ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      let v, assign = create_assign (E_compare (x_1, x_2)) in
      (assign, push v env')
  | I_eq ->
      let x, env' = pop env in
      let v, assign = create_assign (E_eq x) in
      (assign, push v env')
  | I_neq ->
      let x, env' = pop env in
      let v, assign = create_assign (E_neq x) in
      (assign, push v env')
  | I_lt ->
      let x, env' = pop env in
      let v, assign = create_assign (E_lt x) in
      (assign, push v env')
  | I_gt ->
      let x, env' = pop env in
      let v, assign = create_assign (E_gt x) in
      (assign, push v env')
  | I_le ->
      let x, env' = pop env in
      let v, assign = create_assign (E_leq x) in
      (assign, push v env')
  | I_ge ->
      let x, env' = pop env in
      let v, assign = create_assign (E_geq x) in
      (assign, push v env')
  | I_self ->
      let v, assign = create_assign E_self in
      (assign, push v env)
  | I_contract _ ->
      let x, env' = pop env in
      let v, assign = create_assign (E_contract_of_address x) in
      (assign, push v env')
  | I_transfer_tokens ->
      let x, env' = pop env in
      let amount, env' = pop env' in
      let contract, env' = pop env' in
      let operation = O_transfer_tokens (x, amount, contract) in
      let v, assign = create_assign (E_operation operation) in
      (assign, push v env')
  | I_set_delegate ->
      let x, env' = pop env in
      let o = O_set_delegate x in
      let v, assign = create_assign (E_operation o) in
      (assign, push v env')
  | I_create_account ->
      let manager, env' = pop env in
      let delegate, env' = pop env' in
      let delegatable, env' = pop env' in
      let amount, env' = pop env' in
      let o = O_create_account (manager, delegate, delegatable, amount) in
      let v_o, assign_o = create_assign (E_operation o) in
      let v_a, assign_a = create_assign (E_create_account_address o) in
      (create_stmt (S_seq (assign_o, assign_a)), push v_o (push v_a env'))
  | I_create_contract c ->
      let delegate, env' = pop env in
      let amount, env' = pop env' in
      let storage, env' = pop env' in
      let o = O_create_contract (c, delegate, amount, storage) in
      let v_o, assign_o = create_assign (E_operation o) in
      let v_a, assign_a = create_assign (E_create_account_address o) in
      let env' = push v_o (push v_a env') in
      (create_stmt (S_seq (assign_o, assign_a)), env')
  | I_implicit_account ->
      let x, env' = pop env in
      let v, assign = create_assign (E_implicit_account x) in
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
        create_assign (E_check_signature (key, signature, bytes))
      in
      (assign, push v env')
  | I_blake2b ->
      let x, env' = pop env in
      let v, assign = create_assign (E_blake2b x) in
      (assign, push v env')
  | I_sha256 ->
      let x, env' = pop env in
      let v, assign = create_assign (E_sha256 x) in
      (assign, push v env')
  | I_sha512 ->
      let x, env' = pop env in
      let v, assign = create_assign (E_sha512 x) in
      (assign, push v env')
  | I_hash_key ->
      let x, env' = pop env in
      let v, assign = create_assign (E_hash_key x) in
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
      let v, assign = create_assign (E_address_of_contract x) in
      (assign, push v env')
  | I_isnat ->
      let x, env' = pop env in
      let v, assign = create_assign (E_isnat x) in
      (assign, push v env')
  | I_int ->
      let x, env' = pop env in
      let v, assign = create_assign (E_int_of_nat x) in
      (assign, push v env')
  | I_chain_id ->
      let v, assign = create_assign E_chain_id in
      (assign, push v env)
  | I_noop -> (create_stmt S_skip, env)
  | I_unpair ->
      let x, env' = pop env in
      let v_1, assign_1 = create_assign (E_car x) in
      let v_2, assign_2 = create_assign (E_cdr x) in
      (create_stmt (S_seq (assign_1, assign_2)), push v_1 (push v_2 env'))

let convert_program p =
  let counter = ref Z.minus_one in
  let env = Env.push "parameter_storage" Env.empty_env in
  fst (inst_to_stmt counter env (p.Michelson.Adt.code, []))
