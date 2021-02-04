open Michelson.Adt
open Adt

let type_expr = function
  | E_abs _ | E_shiftL (_, _) | E_shiftR (_, _) -> typ_of_typ_t T_nat
  | E_unit -> typ_of_typ_t T_unit
  | E_now -> typ_of_typ_t T_timestamp
  | E_self | E_amount | E_balance -> typ_of_typ_t T_mutez
  | E_source | E_sender -> typ_of_typ_t T_address
  | E_chain_id -> typ_of_typ_t T_chain_id
  | E_special_nil_list t -> ((), T_list t, [])
  | E_push (_, (_, t, _)) -> typ_of_typ_t t
  | E_car v -> (
      match v.var_type with _, T_pair (t, _), _ -> t | _ -> assert false )
  | E_cdr v -> (
      match v.var_type with _, T_pair (_, t), _ -> t | _ -> assert false )
  | E_neg _ | E_compare (_, _) -> typ_of_typ_t T_int
  | E_and (v_1, v_2) -> (
      match (typ_t_of_typ v_1.var_type, typ_t_of_typ v_2.var_type) with
      | T_bool, T_bool -> typ_of_typ_t T_bool
      | T_nat, T_nat | T_int, T_nat -> typ_of_typ_t T_nat
      | _ -> assert false )
  | E_or (v_1, v_2) -> (
      match (typ_t_of_typ v_1.var_type, typ_t_of_typ v_2.var_type) with
      | T_bool, T_bool -> typ_of_typ_t T_bool
      | T_nat, T_nat -> typ_of_typ_t T_nat
      | _ -> assert false )
  | E_xor (v_1, v_2) -> (
      match (typ_t_of_typ v_1.var_type, typ_t_of_typ v_2.var_type) with
      | T_bool, T_bool -> typ_of_typ_t T_bool
      | T_nat, T_nat -> typ_of_typ_t T_nat
      | _ -> assert false )
  | E_eq _ | E_neq _ | E_lt _ | E_gt _ | E_leq _ | E_geq _ | E_not _
  | E_mem (_, _) ->
      typ_of_typ_t T_bool
  | E_add (v_1, v_2) -> (
      match (typ_t_of_typ v_1.var_type, typ_t_of_typ v_2.var_type) with
      | T_nat, T_nat -> typ_of_typ_t T_nat
      | T_nat, T_int | T_int, T_nat | T_int, T_int -> typ_of_typ_t T_int
      | T_timestamp, T_int | T_int, T_timestamp -> typ_of_typ_t T_timestamp
      | T_mutez, T_mutez -> typ_of_typ_t T_mutez
      | _ -> assert false )
  | E_sub (v_1, v_2) -> (
      match (typ_t_of_typ v_1.var_type, typ_t_of_typ v_2.var_type) with
      | T_nat, T_nat
      | T_nat, T_int
      | T_int, T_nat
      | T_int, T_int
      | T_timestamp, T_timestamp ->
          typ_of_typ_t T_int
      | T_timestamp, T_int -> typ_of_typ_t T_timestamp
      | T_mutez, T_mutez -> typ_of_typ_t T_mutez
      | _ -> assert false )
  | E_mul (v_1, v_2) -> (
      match (typ_t_of_typ v_1.var_type, typ_t_of_typ v_2.var_type) with
      | T_nat, T_nat -> typ_of_typ_t T_nat
      | T_nat, T_int | T_int, T_nat | T_int, T_int -> typ_of_typ_t T_int
      | T_mutez, T_nat | T_nat, T_mutez -> typ_of_typ_t T_mutez
      | _ -> assert false )
  | E_div (v_1, v_2) -> (
      match (typ_t_of_typ v_1.var_type, typ_t_of_typ v_2.var_type) with
      | T_nat, T_nat ->
          typ_of_typ_t
            (T_option
               (typ_of_typ_t (T_pair (typ_of_typ_t T_nat, typ_of_typ_t T_nat))))
      | T_nat, T_int | T_int, T_nat | T_int, T_int ->
          typ_of_typ_t
            (T_option
               (typ_of_typ_t (T_pair (typ_of_typ_t T_int, typ_of_typ_t T_nat))))
      | T_mutez, T_nat ->
          typ_of_typ_t
            (T_option
               (typ_of_typ_t
                  (T_pair (typ_of_typ_t T_mutez, typ_of_typ_t T_mutez))))
      | T_mutez, T_mutez ->
          typ_of_typ_t
            (T_option
               (typ_of_typ_t
                  (T_pair (typ_of_typ_t T_nat, typ_of_typ_t T_mutez))))
      | _ -> assert false )
  | E_cons (_, v) -> v.var_type
  | E_operation _ -> typ_of_typ_t T_operation
  | E_pair (v_1, v_2) -> typ_of_typ_t (T_pair (v_1.var_type, v_2.var_type))
  | E_left (v, t) -> typ_of_typ_t (T_or (v.var_type, t))
  | E_right (v, t) -> typ_of_typ_t (T_or (t, v.var_type))
  | E_some v -> typ_of_typ_t (T_option v.var_type)
  | E_none t -> typ_of_typ_t (T_option t)
  | E_get (_, v) -> (
      match typ_t_of_typ v.var_type with
      | T_map (_, t) | T_big_map (_, t) -> t
      | _ -> assert false )
  | E_update (_, _, v) -> v.var_type
  | E_concat (v, _) -> v.var_type
  | E_concat_list v -> (
      match typ_t_of_typ v.var_type with T_list t -> t | _ -> assert false )
  | E_slice (_, _, v) -> typ_of_typ_t (T_option v.var_type)
  | E_pack _ -> typ_of_typ_t T_bytes
  | E_unpack (t, _) -> t
  | E_contract_of_address (t, _) -> t
  | E_implicit_account _ -> typ_of_typ_t (T_contract (typ_of_typ_t T_unit))
  | E_check_signature _ -> typ_of_typ_t T_bool
  | E_blake2b _ | E_sha256 _ | E_sha512 _ -> typ_of_typ_t T_bytes
  | E_hash_key _ -> typ_of_typ_t T_key_hash
  | E_address_of_contract _ | E_create_contract_address _ ->
      typ_of_typ_t T_address
  | E_unlift_option v -> (
      match typ_t_of_typ v.var_type with T_option t -> t | _ -> assert false )
  | E_unlift_or_left v -> (
      match typ_t_of_typ v.var_type with T_or (t, _) -> t | _ -> assert false )
  | E_unlift_or_right v -> (
      match typ_t_of_typ v.var_type with T_or (_, t) -> t | _ -> assert false )
  | E_hd v -> (
      match typ_t_of_typ v.var_type with T_list t -> t | _ -> assert false )
  | E_tl v -> v.var_type
  | E_size _ -> typ_of_typ_t T_nat
  | E_isnat _ -> typ_of_typ_t (T_option (typ_of_typ_t T_nat))
  | E_int_of_nat _ -> typ_of_typ_t T_int
  | E_lambda (t_1, t_2, _) -> typ_of_typ_t (T_lambda (t_1, t_2))
  | E_exec (_, v) -> (
      match typ_t_of_typ v.var_type with
      | T_lambda (_, t) -> t
      | _ -> assert false )
  | E_dup v -> v.var_type
  | E_nil t -> typ_of_typ_t (T_list t)
  | E_empty_set t -> typ_of_typ_t (T_set t)
  | E_empty_map (k_t, v_t) -> typ_of_typ_t (T_map (k_t, v_t))
  | E_empty_big_map (k_t, v_t) -> typ_of_typ_t (T_big_map (k_t, v_t))
  | E_apply (_, l) -> (
      match typ_t_of_typ l.var_type with
      | T_lambda ((_, T_pair (_, b), _), c) -> typ_of_typ_t (T_lambda (b, c))
      | _ -> assert false )
  | E_append (v, _) -> v.var_type
  | E_phi (v, _) -> v.var_type
