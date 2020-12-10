open Env

let join counter env_t env_f =
  let open Adt in
  match (env_t, env_f) with
  | Failed, env | env, Failed -> (env, create_stmt S_skip)
  | Stack env_t, Stack env_f ->
      let env_after =
        List.map2
          (fun v_t v_f ->
            if v_t.var_name = v_f.var_name then v_t
            else { var_name = next_var counter; var_type = v_t.var_type })
          env_t env_f
      in
      let rec phi acc env_after env_t env_f =
        match (env_after, env_t, env_f) with
        | [], [], [] -> acc
        | v_after :: env_after, v_t :: env_t, v_f :: env_f
          when v_t.var_name <> v_f.var_name ->
            let s = create_stmt (S_assign (v_after, E_phi (v_t, v_f))) in
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

let unlift_option_t t =
  let open Michelson.Adt in
  match t with
  | T_option t -> t
  | _ ->
      let () =
        Format.fprintf Format.err_formatter "Expected: option 'a but got %s\n"
          (Pp.string_of_typ t)
      in
      assert false

let car_t t =
  let open Michelson.Adt in
  match t with
  | T_pair (t, _) -> t
  | _ ->
      let () =
        Format.fprintf Format.err_formatter "Expected: pair 'a 'b but got %s\n"
          (Pp.string_of_typ t)
      in
      assert false

let cdr_t t =
  let open Michelson.Adt in
  match t with
  | T_pair (_, t) -> t
  | _ ->
      let () =
        Format.fprintf Format.err_formatter "Expected: pair 'a 'b but got %s\n"
          (Pp.string_of_typ t)
      in
      assert false

let unlift_left_t t =
  let open Michelson.Adt in
  match t with
  | T_or (t, _) -> t
  | _ ->
      let () =
        Format.fprintf Format.err_formatter "Expected: or 'a 'b but got %s\n"
          (Pp.string_of_typ t)
      in
      assert false

let unlift_right_t t =
  let open Michelson.Adt in
  match t with
  | T_or (_, t) -> t
  | _ ->
      let () =
        Format.fprintf Format.err_formatter "Expected: or 'a 'b but got %s\n"
          (Pp.string_of_typ t)
      in
      assert false

let list_elem_t t =
  let open Michelson.Adt in
  match t with
  | T_list t -> t
  | _ ->
      let () =
        Format.fprintf Format.err_formatter "Expected: list 'a but got %s\n"
          (Pp.string_of_typ t)
      in
      assert false

let map_iter_elem_t t =
  let open Michelson.Adt in
  match t with
  | T_list t -> t
  | T_set t -> t
  | T_map (k, v) | T_big_map (k, v) -> T_pair (k, v)
  | _ ->
      let () =
        Format.fprintf Format.err_formatter
          "Expected: list 'a or set 'a or map 'a 'b but got %s"
          (Pp.string_of_typ t)
      in
      assert false

let lambda_t t =
  let open Michelson.Adt in
  match t with
  | T_lambda (_, t) -> t
  | _ ->
      let () =
        Format.fprintf Format.err_formatter
          "Expected: lambda 'a 'b but got %s\n" (Pp.string_of_typ t)
      in
      assert false

let rec inst_to_stmt contract_t counter env =
  let inst_to_stmt = inst_to_stmt contract_t in
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
    let var_name = next_var () in
    let var_type = Typer.type_expr e in
    let v = { var_name; var_type } in
    (v, create_stmt (S_assign (v, e)))
  in
  let rec aux i =
    try
      match i with
      | I_push (t, x) ->
          assert (Michelson.Adt.assert_type x t);
          let e = E_push (x, t) in
          let v, assign = create_assign e in
          (assign, push v env)
      | I_seq (i_1, i_2) ->
          let s_1, env_1 = inst_to_stmt counter env i_1 in
          let s_2, env_2 = inst_to_stmt counter env_1 i_2 in
          (create_stmt (S_seq (s_1, s_2)), env_2)
      | I_drop ->
          let v, env' = pop env in
          (create_stmt (S_drop [ v ]), env')
      | I_drop_n n ->
          let env', l =
            loop_n
              (fun (env, l) _ ->
                let v, env = pop env in
                (env, v :: l))
              (env, []) n
          in
          (create_stmt (S_drop l), env')
      | I_dup ->
          let v = peek env in
          let v', assign = create_assign (E_dup v) in
          (assign, push v' env)
      | I_dig n -> (create_stmt S_dig, dig env n)
      | I_dug n -> (create_stmt S_dug, dug env n)
      | I_swap ->
          let env' = swap env in
          (create_stmt S_swap, env')
      | I_some ->
          let v, env' = pop env in
          let v', assign = create_assign (E_some v) in
          (assign, push v' env')
      | I_none t ->
          let v, assign = create_assign (E_none t) in
          (assign, push v env)
      | I_unit ->
          let v, assign = create_assign E_unit in
          (assign, push v env)
      | I_if_none (i_t, i_f) ->
          let v, env' = pop env in
          let s_t, env_t = inst_to_stmt counter env' i_t in
          let v', assign = create_assign (E_unlift_option v) in
          let s_f, env_f = inst_to_stmt counter (push v' env') i_f in
          let env', phis = join counter env_t env_f in
          let s_f = create_stmt (S_seq (assign, s_f)) in
          let s =
            create_stmt (S_seq (create_stmt (S_if_none (v, s_t, s_f)), phis))
          in
          (s, env')
      | I_if_some (i_t, i_f) -> aux (I_if_none (i_f, i_t))
      | I_pair ->
          let v_1, env' = pop env in
          let t_2, env' = pop env' in
          let v, assign = create_assign (E_pair (v_1, t_2)) in
          (assign, push v env')
      | I_car ->
          let v, env' = pop env in
          let v', assign = create_assign (E_car v) in
          (assign, push v' env')
      | I_cdr ->
          let v, env' = pop env in
          let v', assign = create_assign (E_cdr v) in
          (assign, push v' env')
      | I_left t_r ->
          let v, env' = pop env in
          let v', assign = create_assign (E_left (v, t_r)) in
          (assign, push v' env')
      | I_right t_l ->
          let v, env' = pop env in
          let v', assign = create_assign (E_right (v, t_l)) in
          (assign, push v' env')
      | I_if_left (i_t, i_f) ->
          let v, env' = pop env in
          let e_l = E_unlift_or_left v in
          let e_r = E_unlift_or_left v in
          let v_l, assign_l = create_assign e_l in
          let v_r, assign_r = create_assign e_r in
          let env_t = push v_l env' in
          let env_f = push v_r env' in
          let s_t, env_t = inst_to_stmt counter env_t i_t in
          let s_f, env_f = inst_to_stmt counter env_f i_f in
          let env', phis = join counter env_t env_f in
          let s_t = create_stmt (S_seq (assign_l, s_t)) in
          let s_f = create_stmt (S_seq (assign_r, s_f)) in
          let s =
            create_stmt (S_seq (create_stmt (S_if_left (v, s_t, s_f)), phis))
          in
          (s, env')
      | I_if_right (i_t, i_f) -> inst_to_stmt counter env (I_if_left (i_f, i_t))
      | I_nil t ->
          let v, assign = create_assign (E_nil t) in
          (assign, push v env)
      | I_cons ->
          let v_1, env' = pop env in
          let v_2, env' = pop env' in
          let v, assign = create_assign (E_cons (v_1, v_2)) in
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
            create_stmt
              (S_seq (assign_hd, create_stmt (S_seq (assign_tl, s_t))))
          in
          let s =
            create_stmt (S_seq (create_stmt (S_if_cons (c, s_t, s_f)), phis))
          in
          (s, env')
      | I_size ->
          let v, env' = pop env in
          let v', assign = create_assign (E_size v) in
          (assign, push v' env')
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
          let empty_list, empty_list_assign =
            create_assign (E_special_nil_list c.var_type)
          in
          let loop_var = { var_name = next_var (); var_type = c.var_type } in
          let hd, assign_hd = create_assign (E_hd loop_var) in
          let body, env' =
            let body_env = push hd env' in
            inst_to_stmt counter body_env b
          in
          let tl, assign_tl = create_assign (E_tl loop_var) in
          let x, env' = pop env' in
          let result = { var_name = next_var (); var_type = x.var_type } in
          let append, assign_append = create_assign (E_append (result, x)) in
          let body =
            create_stmt
              (S_seq
                 ( assign_hd,
                   create_stmt
                     (S_seq
                        (body, create_stmt (S_seq (assign_append, assign_tl))))
                 ))
          in
          let s =
            create_stmt
              (S_seq
                 ( empty_list_assign,
                   create_stmt
                     (S_map
                        ( (loop_var, (c, tl)),
                          (result, (empty_list, append)),
                          body )) ))
          in
          (s, push result env')
      | I_iter b ->
          let c, env' = pop env in
          let loop_var = { var_name = next_var (); var_type = c.var_type } in
          let hd, assign_hd = create_assign (E_hd loop_var) in
          let body, env' =
            let body_env = push hd env' in
            inst_to_stmt counter body_env b
          in
          let tl, assign_tl = create_assign (E_tl loop_var) in
          let body =
            create_stmt
              (S_seq (assign_hd, create_stmt (S_seq (body, assign_tl))))
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
          let s =
            create_stmt (S_seq (create_stmt (S_if (c, s_t, s_f)), phis))
          in
          (s, env')
      | I_loop i ->
          let c, env' = pop env in
          let loop_var = { var_name = next_var (); var_type = c.var_type } in
          let body, env' = inst_to_stmt counter env' i in
          let loop_result, env' = pop env' in
          let s = create_stmt (S_loop (loop_var, (c, loop_result), body)) in
          (s, env')
      | I_loop_left i ->
          let c, env' = pop env in
          let loop_var = { var_name = next_var (); var_type = c.var_type } in
          let e = E_unlift_or_left loop_var in
          let v, assign_unlift = create_assign e in
          let body, env' =
            let body_env = push v env' in
            inst_to_stmt counter body_env i
          in
          let loop_result, env' = pop env' in
          let body = create_stmt (S_seq (assign_unlift, body)) in
          let post_loop_unlift = E_unlift_or_right loop_var in
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
          let b, lambda_env =
            let v =
              {
                (*TODO: check this *) var_name = "param_storage";
                var_type = t_1;
              }
            in
            inst_to_stmt counter (push v empty_env) i
          in
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
      | I_cast _ -> (create_stmt S_skip, env)
      | I_rename -> (create_stmt S_skip, env)
      | I_concat ->
          let v, env' = pop env in
          let (v', assign), env' =
            match v.var_type with
            | T_list T_string -> (create_assign (E_concat_list v), env')
            | T_string ->
                let s_2, env' = pop env' in
                (create_assign (E_concat (v, s_2)), env')
            | _ -> assert false
          in
          (assign, push v' env')
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
          let v, env' = pop env in
          let v', assign = create_assign (E_unpack (t, v)) in
          (assign, push v' env')
      | I_add ->
          let v_1, env' = pop env in
          let v_2, env' = pop env' in
          let v, assign = create_assign (E_add (v_1, v_2)) in
          (assign, push v env')
      | I_sub ->
          let v_1, env' = pop env in
          let v_2, env' = pop env' in
          let v, assign = create_assign (E_sub (v_1, v_2)) in
          (assign, push v env')
      | I_mul ->
          let t_1, env' = pop env in
          let t_2, env' = pop env' in
          let v, assign = create_assign (E_mul (t_1, t_2)) in
          (assign, push v env')
      | I_ediv ->
          let v_1, env' = pop env in
          let v_2, env' = pop env' in
          let v, assign = create_assign (E_div (v_1, v_2)) in
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
      | I_contract t ->
          let x, env' = pop env in
          let v, assign = create_assign (E_contract_of_address (t, x)) in
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
      | I_create_contract c ->
          let delegate, env' = pop env in
          let amount, env' = pop env' in
          let storage, env' = pop env' in
          let o = O_create_contract (c, delegate, amount, storage) in
          let v_o, assign_o = create_assign (E_operation o) in
          let v_a, assign_a =
            create_assign
              (E_create_contract_address (c, delegate, amount, storage))
          in
          let env' =
            push
              (v_o, create_typ T_operation)
              (push (v_a, create_typ T_address) env')
          in
          (create_stmt (S_seq (assign_o, assign_a)), env')
      | I_implicit_account ->
          let (x, _), env' = pop env in
          let v, assign = create_assign (E_implicit_account x) in
          (assign, push (v, create_typ (T_contract (create_typ T_unit))) env')
      | I_now ->
          let v, assign = create_assign E_now in
          (assign, push (v, create_typ T_timestamp) env)
      | I_amount ->
          let v, assign = create_assign E_amount in
          (assign, push (v, create_typ T_mutez) env)
      | I_balance ->
          let v, assign = create_assign E_balance in
          (assign, push (v, create_typ T_mutez) env)
      | I_check_signature ->
          let (key, _), env' = pop env in
          let (signature, _), env' = pop env' in
          let (bytes, _), env' = pop env' in
          let v, assign =
            create_assign (E_check_signature (key, signature, bytes))
          in
          (assign, push (v, create_typ T_bool) env')
      | I_blake2b ->
          let (x, _), env' = pop env in
          let v, assign = create_assign (E_blake2b x) in
          (assign, push (v, create_typ T_bytes) env')
      | I_sha256 ->
          let (x, _), env' = pop env in
          let v, assign = create_assign (E_sha256 x) in
          (assign, push (v, create_typ T_bytes) env')
      | I_sha512 ->
          let (x, _), env' = pop env in
          let v, assign = create_assign (E_sha512 x) in
          (assign, push (v, create_typ T_bytes) env')
      | I_hash_key ->
          let (x, _), env' = pop env in
          let v, assign = create_assign (E_hash_key x) in
          (assign, push (v, create_typ T_key_hash) env')
      | I_source ->
          let v, assign = create_assign E_source in
          (assign, push (v, create_typ T_address) env)
      | I_sender ->
          let v, assign = create_assign E_sender in
          (assign, push (v, create_typ T_address) env)
      | I_address ->
          let (x, _), env' = pop env in
          let v, assign = create_assign (E_address_of_contract x) in
          (assign, push (v, create_typ T_address) env')
      | I_isnat ->
          let (x, _), env' = pop env in
          let v, assign = create_assign (E_isnat x) in
          (assign, push (v, create_typ (T_option (create_typ T_nat))) env')
      | I_int ->
          let (x, _), env' = pop env in
          let v, assign = create_assign (E_int_of_nat x) in
          (assign, push (v, create_typ T_int) env')
      | I_chain_id ->
          let v, assign = create_assign E_chain_id in
          (assign, push (v, create_typ T_chain_id) env)
      | I_noop -> (create_stmt S_skip, env)
      | I_unpair ->
          let (x, t), env' = pop env in
          let v_1, assign_1 = create_assign (E_car x) in
          let v_2, assign_2 = create_assign (E_cdr x) in
          let t_1, t_2 = (car_t t, cdr_t t) in
          ( create_stmt (S_seq (assign_1, assign_2)),
            push (v_1, t_1) (push (v_2, t_2) env') )
    with exn -> raise exn
  in
  aux

let convert_program counter p =
  let open Michelson.Adt in
  let env =
    Env.push
      { var_name = "parameter_storage"; var_type = T_pair (p.param, p.storage) }
      Env.empty_env
  in
  fst (inst_to_stmt p.param counter env p.code) |> Adt.simpl
