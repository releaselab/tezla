type comparable_type =
  | T_int
  | T_nat
  | T_string
  | T_bytes
  | T_mutez
  | T_bool
  | T_key_hash
  | T_timestamp
  | T_address

and typ =
  | T_comparable of comparable_type node
  | T_key
  | T_unit
  | T_signature
  | T_option of typ node
  | T_list of typ node
  | T_set of comparable_type node
  | T_operation
  | T_contract of typ node
  | T_pair of typ node * typ node
  | T_or of typ node * typ node
  | T_lambda of typ node * typ node
  | T_map of comparable_type node * typ node
  | T_big_map of comparable_type node * typ node

and inst =
  | I_seq of inst node * inst node
  | I_drop
  | I_dup
  | I_swap
  | I_push of typ node * data node
  | I_some
  | I_none of typ node
  | I_unit
  | I_if_none of inst node * inst node
  | I_pair
  | I_car
  | I_cdr
  | I_left of typ node
  | I_right of typ node
  | I_if_left of inst node * inst node
  | I_if_right of inst node * inst node
  | I_nil of typ node
  | I_cons
  | I_if_cons of inst node * inst node
  | I_size
  | I_empty_set of comparable_type node
  | I_empty_map of comparable_type node * typ node
  | I_map of inst node
  | I_iter of inst node
  | I_mem
  | I_get
  | I_update
  | I_if of inst node * inst node
  | I_loop of inst node
  | I_loop_left of inst node
  | I_lambda of typ node * typ node * inst node
  | I_exec
  | I_dip of inst node
  | I_failwith of data node
  | I_cast
  | I_rename
  | I_concat
  | I_slice
  | I_pack
  | I_unpack
  | I_add
  | I_sub
  | I_mul
  | I_ediv
  | I_abs
  | I_neg
  | I_lsl
  | I_lsr
  | I_or
  | I_and
  | I_xor
  | I_not
  | I_compare
  | I_eq
  | I_neq
  | I_lt
  | I_gt
  | I_le
  | I_ge
  | I_self
  | I_contract of typ node
  | I_transfer_tokens
  | I_set_delegate
  | I_create_account
  | I_create_contract of inst node
  | I_implicit_account
  | I_now
  | I_amount
  | I_balance
  | I_check_signature
  | I_blake2b
  | I_sha256
  | I_sha512
  | I_hash_key
  | I_steps_to_quota
  | I_source
  | I_sender
  | I_address

and data =
  | D_int of Z.t
  | D_nat of Z.t
  | D_string of string
  | D_timestamp of string
  | D_signature of string
  | D_key of string
  | D_key_hash of string
  | D_mutez of string
  | D_contract of string
  | D_unit
  | D_bool of bool
  | D_pair of data node * data node
  | D_left of data node
  | D_right of data node
  | D_some of data node
  | D_none
  | D_list of data node list
  | D_set of data node list
  | D_map of (data node * data node) list
  | D_instruction of inst node

and _ node_data =
  | Inst : inst -> inst node_data
  | Data : data -> data node_data
  | Type : typ -> typ node_data
  | Comparable_type : comparable_type -> comparable_type node_data

and 'a node = {loc: Location.t; data: 'a node_data}

let get_node_data : type a. a node -> a =
 fun n ->
  match n.data with
  | Inst x ->
      x
  | Data x ->
      x
  | Type x ->
      x
  | Comparable_type x ->
      x

type program =
  {param: typ node; storage: typ node; return: typ node; code: inst node}
