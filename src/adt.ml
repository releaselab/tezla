type comparable_type = Michelson.Adt.comparable_type_annotated

type typ = Michelson.Adt.typ_annotated

type operation =
  | O_create_contract of Michelson.Adt.program * expr * expr * expr
  | O_transfer_tokens of expr * expr * expr
  | O_set_delegate of expr
  | O_create_account of expr * expr * expr * expr

and expr =
  | E_car of expr
  | E_cdr of expr
  | E_abs of expr
  | E_neg of expr
  | E_not of expr
  | E_add of expr * expr
  | E_sub of expr * expr
  | E_mul of expr * expr
  | E_div of expr * expr
  | E_shiftL of expr * expr
  | E_shiftR of expr * expr
  | E_and of expr * expr
  | E_or of expr * expr
  | E_xor of expr * expr
  | E_eq of expr
  | E_neq of expr
  | E_lt of expr
  | E_gt of expr
  | E_leq of expr
  | E_geq of expr
  | E_compare of expr * expr
  | E_ident of string
  | E_cons of expr * expr
  | E_int of Z.t
  | E_nat of Z.t
  | E_string of string
  | E_timestamp of string
  | E_signature of string
  | E_key of string
  | E_key_hash of string
  | E_mutez of Z.t
  | E_operation of operation
  | E_unit
  | E_bool of bool
  | E_pair of expr * expr
  | E_left of expr
  | E_right of expr
  | E_some of expr
  | E_none of typ
  | E_list of typ * expr list
  | E_set of expr list
  | E_map of (expr * expr) list
  | E_big_map of (expr * expr) list
  | E_mem of expr * expr
  | E_get of expr * expr
  | E_update of expr * expr * expr
  | E_cast of expr
  | E_concat of expr * expr
  | E_slice of expr * expr * expr
  | E_pack of expr
  | E_unpack of typ * expr
  | E_self
  | E_contract_of_address of expr
  | E_implicit_account of expr
  | E_now
  | E_amount
  | E_balance
  | E_check_signature of expr * expr * expr
  | E_blake2b of expr
  | E_sha256 of expr
  | E_sha512 of expr
  | E_hash_key of expr
  | E_steps_to_quota
  | E_source
  | E_sender
  | E_address_of_contract of expr
  | E_create_contract_address of operation
  | E_lift_option of expr
  | E_lift_or of expr
  | E_list_hd of expr
  | E_list_tl of expr
  | E_size of expr
  | E_bytes of string
  | E_isnat of expr
  | E_int_of_nat of expr
  | E_chain_id
  | E_create_account_address of operation
  | E_lambda of typ * typ * func
  | E_exec of string * string

and stmt =
  | S_seq of stmt * stmt
  | S_var_decl of string
  | S_assign of string * expr * typ option
  | S_skip
  | S_drop of string
  | S_swap
  | S_if of string * stmt * stmt
  | S_if_none of string * stmt * stmt * string
  | S_if_left of string * stmt * stmt * string
  | S_if_cons of string * stmt * string * string * stmt
  | S_loop of string * stmt
  | S_loop_left of string * stmt
  | S_map of string * stmt
  | S_iter of string * stmt
  | S_failwith of string
  | S_cast
  | S_contract of typ

and func = stmt * string

and program = typ * typ * func
