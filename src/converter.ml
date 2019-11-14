open Env

let string_to_expr s =
  let open Ast in
  create (Expr (E_ident s))

let join_envs_if s_t env_t s_f env_f =
  let open Ast in
  let env = join string_to_expr env_t env_f in
  let decls =
    List.fold_left
      (fun acc n ->
        match get_node_data n with
        | E_ident v ->
            let decl = create (Decl v) in
            create (Stmt (S_seq (acc, create (Stmt (S_var_decl decl)))))
        | _ -> assert false)
      (create (Stmt S_skip)) env
  in
  let assigns_t =
    List.fold_left2
      (fun acc x n ->
        match get_node_data n with
        | E_ident v ->
            create (Stmt (S_seq (acc, create (Stmt (S_assign (v, x))))))
        | _ -> assert false)
      (create (Stmt S_skip)) env_t env
  in
  let assigns_f =
    List.fold_left2
      (fun acc x n ->
        match get_node_data n with
        | E_ident v ->
            create (Stmt (S_seq (acc, create (Stmt (S_assign (v, x))))))
        | _ -> assert false)
      (create (Stmt S_skip)) env_f env
  in
  let s_t' =
    create (Stmt (S_seq (decls, create (Stmt (S_seq (s_t, assigns_t))))))
  in
  let s_f' =
    create (Stmt (S_seq (decls, create (Stmt (S_seq (s_f, assigns_f))))))
  in
  (env, s_t', s_f')

let join_envs_while s env =
  let open Ast in
  let env' = join string_to_expr env env in
  let decls =
    List.fold_left
      (fun acc n ->
        match get_node_data n with
        | E_ident v ->
            let decl = create (Decl v) in
            create (Stmt (S_seq (acc, create (Stmt (S_var_decl decl)))))
        | _ -> assert false)
      (create (Stmt S_skip)) env
  in
  let assigns =
    List.fold_left2
      (fun acc x n ->
        match get_node_data n with
        | E_ident v ->
            create (Stmt (S_seq (acc, create (Stmt (S_assign (v, x))))))
        | _ -> assert false)
      (create (Stmt S_skip)) env env'
  in
  let s' = create (Stmt (S_seq (decls, create (Stmt (S_seq (s, assigns)))))) in
  (env', s')

let comparable_type_converter n =
  let open Michelson.Ast in
  let n' =
    match get_node_data n with
    | T_int -> Ast.T_int
    | T_nat -> Ast.T_nat
    | T_string -> Ast.T_string
    | T_bytes -> Ast.T_bytes
    | T_mutez -> Ast.T_mutez
    | T_bool -> Ast.T_bool
    | T_key_hash -> Ast.T_key_hash
    | T_timestamp -> Ast.T_timestamp
    | T_address -> Ast.T_address
  in
  Ast.create ~loc:n.loc (Comparable_type n')

let rec type_converter n =
  let open Michelson.Ast in
  let n' =
    match get_node_data n with
    | T_comparable t -> Ast.T_comparable (comparable_type_converter t)
    | T_key -> Ast.T_key
    | T_unit -> Ast.T_unit
    | T_signature -> Ast.T_signature
    | T_option t -> Ast.T_option (type_converter t)
    | T_list t -> Ast.T_list (type_converter t)
    | T_set t -> Ast.T_set (comparable_type_converter t)
    | T_operation -> Ast.T_operation
    | T_contract t -> Ast.T_contract (type_converter t)
    | T_pair (t_1, t_2) -> Ast.T_pair (type_converter t_1, type_converter t_2)
    | T_or (t_1, t_2) -> Ast.T_or (type_converter t_1, type_converter t_2)
    | T_lambda (t_1, t_2) ->
        Ast.T_lambda (type_converter t_1, type_converter t_2)
    | T_map (t_1, t_2) ->
        Ast.T_map (comparable_type_converter t_1, type_converter t_2)
    | T_big_map (t_1, t_2) ->
        Ast.T_big_map (comparable_type_converter t_1, type_converter t_2)
    | T_chain_id -> Ast.T_chain_id
  in
  Ast.create ~loc:n.loc (Type n')

let rec data_to_expr d =
  let open Michelson.Ast in
  let open Ast in
  let e =
    match Michelson.Ast.get_node_data d with
    | D_int i -> E_int i
    | D_nat i -> E_nat i
    | D_string s -> E_string s
    | D_timestamp s -> E_timestamp s
    | D_signature s -> E_signature s
    | D_key s -> E_key s
    | D_key_hash s -> E_key_hash s
    | D_mutez s -> E_mutez s
    | D_contract s -> E_contract s
    | D_unit -> E_unit
    | D_bool x -> E_bool x
    | D_pair (x, y) -> E_pair (data_to_expr x, data_to_expr y)
    | D_left x -> E_left (data_to_expr x)
    | D_right x -> E_right (data_to_expr x)
    | D_some x -> E_some (data_to_expr x)
    | D_none -> E_none
    | D_list x -> E_list (List.map (fun e -> data_to_expr e) x)
    | D_set x -> E_set (List.map (fun e -> data_to_expr e) x)
    | D_map x ->
        E_map (List.map (fun (x, y) -> (data_to_expr x, data_to_expr y)) x)
    | D_bytes x -> E_bytes x
    (* | D_instruction x ->
        let s, _ = convert empty_env x in
        E_stmt s *)
  in
  create ~loc:d.loc (Expr e)

and convert env i =
  let open Michelson.Ast in
  let open Ast in
  let create_stmt_node loc s = create ~loc (Stmt s) in
  let create_expr_node ?(loc = Michelson.Location.Unknown) e =
    create ~loc (Expr e)
  in
  let loop_n f =
    let rec loop acc n =
      if Z.(n = zero) then acc else loop (f acc n) Z.(n - one)
    in
    loop
  in
  match Michelson.Ast.get_node_data i with
  | I_seq (i_1, i_2) ->
      let s_1, env_1 = convert env i_1 in
      let s_2, env_2 = convert env_1 i_2 in
      (create_stmt_node i.loc (S_seq (s_1, s_2)), env_2)
  | I_drop -> (create_stmt_node i.loc S_skip, drop env)
  | I_drop_n n ->
      let env' = loop_n (fun acc _ -> drop acc) env n in
      (create_stmt_node i.loc S_skip, env')
  | I_dup ->
      let x = peek env in
      (create_stmt_node i.loc S_skip, push x env)
  | I_dig n -> (create_stmt_node i.loc S_skip, dig env n)
  | I_dug n -> (create_stmt_node i.loc S_skip, dug env n)
  | I_swap ->
      let env' = swap env in
      (create_stmt_node i.loc S_skip, env')
  | I_push (_, x) -> (create_stmt_node i.loc S_skip, push (data_to_expr x) env)
  | I_some ->
      let x, env' = pop env in
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_some x)) env')
  | I_none _ ->
      (create_stmt_node i.loc S_skip, push (create_expr_node E_none) env)
  | I_unit -> (create_stmt_node i.loc S_skip, push (create_expr_node E_unit) env)
  | I_if_none (i_t, i_f) ->
      let x, env' = pop env in
      let e = create_expr_node (E_is_none x) in
      let s_t, env_t = convert env' i_t in
      let s_f, env_f =
        convert (push (create_expr_node (E_lift_option x)) env') i_f
      in
      let env', s_t', s_f' = join_envs_if s_t env_t s_f env_f in
      (create_stmt_node i.loc (S_if (e, s_t', s_f')), env')
  | I_pair ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_pair (x_1, x_2))) env' )
  | I_car ->
      let x, env' = pop env in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_unop (Fst, x))) env' )
  | I_cdr ->
      let x, env' = pop env in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_unop (Snd, x))) env' )
  | I_left _ ->
      let x, env' = pop env in
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_left x)) env')
  | I_right _ ->
      let x, env' = pop env in
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_right x)) env')
  | I_if_left (i_t, i_f) ->
      let x, env' = pop env in
      let c = create_expr_node (E_is_left x) in
      let e = create_expr_node (E_lift_or x) in
      let env' = push e env' in
      let s_t, env_t = convert env' i_t in
      let s_f, env_f = convert env' i_f in
      let env', s_t', s_f' = join_envs_if s_t env_t s_f env_f in
      (create_stmt_node i.loc (S_if (c, s_t', s_f')), env')
  | I_if_right (i_t, i_f) ->
      let x, env' = pop env in
      let c = create_expr_node (E_unop (Not, create_expr_node (E_is_left x))) in
      let e = create_expr_node (E_lift_or x) in
      let env' = push e env' in
      let s_t, env_t = convert env' i_t in
      let s_f, env_f = convert env' i_f in
      let env', s_t', s_f' = join_envs_if s_t env_t s_f env_f in
      (create_stmt_node i.loc (S_if (c, s_t', s_f')), env')
  | I_nil _ ->
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_list [])) env)
  | I_cons ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_cons (x_1, x_2))) env' )
  | I_if_cons (i_t, i_f) ->
      let x, env_t = pop env in
      let c = create_expr_node (E_is_list_empty x) in
      let env_f =
        push
          (create_expr_node (E_list_hd x))
          (push (create_expr_node (E_list_tl x)) env_t)
      in
      let s_t, env_t' = convert env_t i_t in
      let s_f, env_f' = convert env_f i_f in
      let env', s_t', s_f' = join_envs_if s_t env_t' s_f env_f' in
      (create_stmt_node i.loc (S_if (c, s_t', s_f')), env')
  | I_size ->
      let x, env' = pop env in
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_size x)) env')
  | I_empty_set _ ->
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_set [])) env)
  | I_empty_map _ ->
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_map [])) env)
  | I_empty_big_map _ ->
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_big_map [])) env)
  | I_map i ->
      let _ = convert empty_env i in
      (create_stmt_node i.loc S_todo, env)
  | I_iter _ -> (create_stmt_node i.loc S_todo, env)
  | I_mem ->
      let elt, env' = pop env in
      let set, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_mem (elt, set))) env' )
  | I_get ->
      let key, env' = pop env in
      let map, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_get (key, map))) env' )
  | I_update ->
      let key, env' = pop env in
      let value, env' = pop env' in
      let map, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_update (key, value, map))) env' )
  | I_if (i_t, i_f) ->
      let c, env' = pop env in
      let s_t, env_t' = convert env' i_t in
      let s_f, env_f' = convert env' i_f in
      let env', s_t', s_f' = join_envs_if s_t env_t' s_f env_f' in
      (create_stmt_node i.loc (S_if (c, s_t', s_f')), env')
  | I_loop i ->
      let c, env' = pop env in
      let s, env' = convert env' i in
      let env', s' = join_envs_while s env' in
      (create_stmt_node i.loc (S_while (c, s')), env')
  | I_loop_left i ->
      let x, env' = pop env in
      let c = create_expr_node (E_is_left x) in
      let e = create_expr_node (E_lift_or x) in
      let s, env' = convert (push e env') i in
      let x', env' = pop env' in
      let e' = create_expr_node (E_lift_or x') in
      let env' = push e' env' in
      let env', s' = join_envs_while s env' in
      (create_stmt_node i.loc (S_while (c, s')), env')
  | I_lambda (_, _, i) ->
      let s, _ = convert empty_env i in
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_stmt s)) env)
  | I_exec -> (create_stmt_node i.loc S_todo, env)
  | I_dip i ->
      let x, env' = pop env in
      let s, env' = convert env' i in
      (s, push x env')
  | I_dip_n (n, i) ->
      let xl, env' = dip env n in
      let s, env' = convert env' i in
      let env' = List.fold_left (fun acc x -> push x acc) env' xl in
      (s, env')
  | I_failwith -> (create_stmt_node i.loc S_todo, env)
  | I_cast -> (create_stmt_node i.loc S_todo, env)
  | I_rename -> (create_stmt_node i.loc S_todo, env)
  | I_concat ->
      let s, env' = pop env in
      let t, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_concat (s, t))) env' )
  | I_slice ->
      let offset, env' = pop env in
      let length, env' = pop env' in
      let x, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_slice (offset, length, x))) env' )
  | I_pack ->
      let x, env' = pop env in
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_pack x)) env')
  | I_unpack t ->
      let x, env' = pop env in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_unpack (type_converter t, x))) env' )
  | I_add ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Add, x_1, x_2))) env' )
  | I_sub ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Sub, x_1, x_2))) env' )
  | I_mul ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Mul, x_1, x_2))) env' )
  | I_ediv ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Div, x_1, x_2))) env' )
  | I_abs ->
      let x, env' = pop env in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_unop (Abs, x))) env' )
  | I_neg ->
      let x, env' = pop env in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_unop (Neg, x))) env' )
  | I_lsl ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (ShiftL, x_1, x_2))) env' )
  | I_lsr ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (ShiftR, x_1, x_2))) env' )
  | I_or ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Or, x_1, x_2))) env' )
  | I_and ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (And, x_1, x_2))) env' )
  | I_xor ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Xor, x_1, x_2))) env' )
  | I_not ->
      let x, env' = pop env in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_unop (Not, x))) env' )
  | I_compare ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Compare, x_1, x_2))) env' )
  | I_eq ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Eq, x_1, x_2))) env' )
  | I_neq ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Neq, x_1, x_2))) env' )
  | I_lt ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Lt, x_1, x_2))) env' )
  | I_gt ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Gt, x_1, x_2))) env' )
  | I_le ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Leq, x_1, x_2))) env' )
  | I_ge ->
      let x_1, env' = pop env in
      let x_2, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_binop (Geq, x_1, x_2))) env' )
  | I_self -> (create_stmt_node i.loc S_skip, push (create_expr_node E_self) env)
  | I_contract _ ->
      let x, env' = pop env in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_contract_of_address x)) env' )
  | I_transfer_tokens ->
      (* let (x,_), env' = pop env in
      let (amount,_), env' = pop env' in
      let (contract,_), env' = pop env' in
      (create_stmt_node (S_skip), push (E_set_delegate x) env') *)
      (create_stmt_node i.loc S_todo, env)
  | I_set_delegate ->
      (* let (x,_), env' = pop env in
      (create_stmt_node (S_skip), push (E_set_delegate x) env') *)
      (create_stmt_node i.loc S_todo, env)
  | I_create_account ->
      let manager, env' = pop env in
      let delegate, env' = pop env' in
      let delegatable, env' = pop env' in
      let amount, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push
          (create
             (Expr (E_create_account (manager, delegate, delegatable, amount))))
          env' )
  | I_create_contract _ -> (create_stmt_node i.loc S_todo, env)
  | I_implicit_account ->
      let x, env' = pop env in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_implicit_account x)) env' )
  | I_now -> (create_stmt_node i.loc S_skip, push (create_expr_node E_now) env)
  | I_amount ->
      (create_stmt_node i.loc S_skip, push (create_expr_node E_amount) env)
  | I_balance ->
      (create_stmt_node i.loc S_skip, push (create_expr_node E_balance) env)
  | I_check_signature ->
      let key, env' = pop env in
      let signature, env' = pop env' in
      let bytes, env' = pop env' in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_check_signature (key, signature, bytes))) env'
      )
  | I_blake2b ->
      let x, env' = pop env in
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_blake2b x)) env')
  | I_sha256 ->
      let x, env' = pop env in
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_sha256 x)) env')
  | I_sha512 ->
      let x, env' = pop env in
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_sha512 x)) env')
  | I_hash_key ->
      let x, env' = pop env in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_hash_key x)) env' )
  | I_steps_to_quota ->
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node E_steps_to_quota) env )
  | I_source ->
      (create_stmt_node i.loc S_skip, push (create_expr_node E_source) env)
  | I_sender ->
      (create_stmt_node i.loc S_skip, push (create_expr_node E_sender) env)
  | I_address ->
      let x, env' = pop env in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_address_of_contact x)) env' )
  | I_isnat ->
      let x, env' = pop env in
      (create_stmt_node i.loc S_skip, push (create_expr_node (E_isnat x)) env')
  | I_int ->
      let x, env' = pop env in
      ( create_stmt_node i.loc S_skip,
        push (create_expr_node (E_int_of_nat x)) env' )
  | I_chain_id ->
      (create_stmt_node i.loc S_skip, push (create_expr_node E_chain_id) env)
  | I_noop -> (create_stmt_node i.loc S_skip, env)

(* | _ -> assert false *)
