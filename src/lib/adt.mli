type typ = (unit, Michelson.Adt.annot list) Michelson.Adt.typ

type data = (unit, Michelson.Adt.annot list) Michelson.Adt.data

type var = { var_name : string; var_type : typ }

type operation =
  | O_create_contract of
      (unit, Michelson.Adt.annot list) Michelson.Adt.program * var * var * var
  | O_transfer_tokens of var * var * var
  | O_set_delegate of var
  | O_create_account of var * var * var * var

and expr =
  | E_push of data * typ
  | E_car of var
  | E_cdr of var
  | E_abs of var
  | E_neg of var
  | E_not of var
  | E_add of var * var
  | E_sub of var * var
  | E_mul of var * var
  | E_div of var * var
  | E_shiftL of var * var
  | E_shiftR of var * var
  | E_and of var * var
  | E_or of var * var
  | E_xor of var * var
  | E_eq of var
  | E_neq of var
  | E_lt of var
  | E_gt of var
  | E_leq of var
  | E_geq of var
  | E_compare of var * var
  | E_cons of var * var
  | E_operation of operation
  | E_unit
  | E_pair of var * var
  | E_left of var * typ
  | E_right of var * typ
  | E_some of var
  | E_none of typ
  | E_mem of var * var
  | E_get of var * var
  | E_update of var * var * var
  | E_concat of var * var
  | E_concat_list of var
  | E_slice of var * var * var
  | E_pack of var
  | E_unpack of typ * var
  | E_self
  | E_contract_of_address of typ * var
  | E_implicit_account of var
  | E_now
  | E_amount
  | E_balance
  | E_check_signature of var * var * var
  | E_blake2b of var
  | E_sha256 of var
  | E_sha512 of var
  | E_hash_key of var
  | E_source
  | E_sender
  | E_address_of_contract of var
  | E_create_contract_address of program * var * var * var
  | E_unlift_option of var
  | E_unlift_or_left of var
  | E_unlift_or_right of var
  | E_hd of var
  | E_tl of var
  | E_size of var
  | E_isnat of var
  | E_int_of_nat of var
  | E_chain_id
  | E_lambda of typ * typ * func
  | E_exec of var * var
  | E_dup of var
  | E_nil of typ
  | E_empty_set of typ
  | E_empty_map of typ * typ
  | E_empty_big_map of typ * typ
  | E_apply of var * var
  | E_append of var * var
  | E_special_nil_list of typ
  | E_phi of var * var

and stmt_t =
  | S_seq of stmt * stmt
  | S_assign of var * expr
  | S_skip
  | S_drop of var list
  | S_swap
  | S_dig
  | S_dug
  | S_if of var * stmt * stmt
  | S_if_none of var * stmt * stmt
  | S_if_left of var * stmt * stmt
  | S_if_cons of var * stmt * stmt
  | S_loop of var * (var * var) * stmt
  | S_loop_left of var * (var * var) * stmt
  | S_map of (var * (var * var)) * (var * (var * var)) * stmt
  | S_iter of var * (var * var) * stmt
  | S_failwith of var

and stmt = { id : int; stm : stmt_t }

and func = stmt * var

and program = typ * typ * stmt

val create_stmt : stmt_t -> stmt

val simpl : stmt -> stmt

val typ_t_of_typ : typ -> (unit, Michelson.Adt.annot list) Michelson.Adt.typ_t

val typ_of_typ_t : (unit, Michelson.Adt.annot list) Michelson.Adt.typ_t -> typ
