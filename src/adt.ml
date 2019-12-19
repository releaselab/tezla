(* let sprint_list ?(first = "[") ?(last = "]") ?(sep = "; ") to_string l =
  let strout = BatIO.output_string () in
  List.print ~first ~last ~sep
    (fun outch x -> to_string x |> String.print outch)
    strout l ;
  BatIO.close_out strout *)

type ident = string

type decl = ident

type unop = Fst | Snd | Abs | Neg | Not

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Eq
  | ShiftL
  | ShiftR
  | And
  | Or
  | Xor
  | Neq
  | Lt
  | Gt
  | Leq
  | Geq
  | Compare

type comparable_type = Michelson.Adt.comparable_type_annotated

type typ = Michelson.Adt.typ_annotated

and operation =
  | O_create_contract of Michelson.Adt.program * expr * expr * expr
  | O_transfer_tokens of expr * expr * expr
  | O_set_delegate of expr
  | O_create_account of expr * expr * expr * expr

and expr =
  | E_unop of unop * expr
  | E_binop of binop * expr * expr
  | E_ident of string
  | E_cons of expr * expr
  | E_int of Z.t
  | E_nat of Z.t
  | E_string of string
  | E_timestamp of string
  | E_signature of string
  | E_key of string
  | E_key_hash of string
  | E_mutez of string
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
  | E_is_none of expr
  | E_lift_option of expr
  | E_is_left of expr
  | E_lift_or of expr
  | E_is_cons of expr
  | E_list_hd of expr
  | E_list_tl of expr
  | E_size of expr
  | E_bytes of string
  | E_isnat of expr
  | E_int_of_nat of expr
  | E_chain_id
  | E_create_account_address of operation
  | E_lambda of func

and stmt =
  | S_seq of stmt * stmt
  | S_var_decl of ident
  | S_assign of string * expr * typ option
  | S_skip
  | S_drop of ident
  | S_dup of ident
  | S_if of ident * stmt * stmt
  | S_if_none of ident * stmt * stmt * ident
  | S_if_left of ident * stmt * stmt * ident
  | S_if_cons of ident * stmt * ident * ident * stmt
  | S_loop of ident * stmt
  | S_loop_left of ident * stmt
  | S_map of ident * stmt
  | S_iter of ident * stmt
  | S_exec of stmt * ident
  | S_failwith of ident
  | S_cast
  | S_contract of typ

and func = stmt * ident

and program = typ * typ * func
