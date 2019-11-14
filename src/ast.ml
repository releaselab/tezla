open Batteries

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
  | T_comparable of comparable_type t
  | T_key
  | T_unit
  | T_signature
  | T_option of typ t
  | T_list of typ t
  | T_set of comparable_type t
  | T_operation
  | T_contract of typ t
  | T_pair of typ t * typ t
  | T_or of typ t * typ t
  | T_lambda of typ t * typ t
  | T_map of comparable_type t * typ t
  | T_big_map of comparable_type t * typ t
  | T_chain_id

and expr =
  | E_unop of unop * expr t
  | E_binop of binop * expr t * expr t
  | E_ident of string
  | E_cons of expr t * expr t
  | E_int of Z.t
  | E_nat of Z.t
  | E_string of string
  | E_timestamp of string
  | E_signature of string
  | E_key of string
  | E_key_hash of string
  | E_mutez of string
  | E_contract of string
  | E_unit
  | E_bool of bool
  | E_pair of expr t * expr t
  | E_left of expr t
  | E_right of expr t
  | E_some of expr t
  | E_none
  | E_list of expr t list
  | E_set of expr t list
  | E_map of (expr t * expr t) list
  | E_big_map of (expr t * expr t) list
  | E_stmt of stmt t
  | E_mem of expr t * expr t
  | E_get of expr t * expr t
  | E_update of expr t * expr t * expr t
  | E_cast of expr t
  | E_concat of expr t * expr t
  | E_slice of expr t * expr t * expr t
  | E_pack of expr t
  | E_unpack of typ t * expr t
  | E_self
  | E_contract_of_address of expr t
  | E_set_delegate of expr t
  | E_create_account of expr t * expr t * expr t * expr t
  | E_implicit_account of expr t
  | E_now
  | E_amount
  | E_balance
  | E_check_signature of expr t * expr t * expr t
  | E_blake2b of expr t
  | E_sha256 of expr t
  | E_sha512 of expr t
  | E_hash_key of expr t
  | E_steps_to_quota
  | E_source
  | E_sender
  | E_address_of_contact of expr t
  | E_is_none of expr t
  | E_lift_option of expr t
  | E_is_left of expr t
  | E_lift_or of expr t
  | E_is_list_empty of expr t
  | E_list_hd of expr t
  | E_list_tl of expr t
  | E_size of expr t
  | E_bytes of string
  | E_isnat of expr t
  | E_int_of_nat of expr t
  | E_chain_id

and stmt =
  | S_seq of stmt t * stmt t
  | S_var_decl of decl t
  | S_assign of string * expr t
  | S_skip
  | S_if of expr t * stmt t * stmt t
  | S_while of expr t * stmt t
  | S_if_cons of stmt t * stmt t
  | S_size
  | S_empty_set of comparable_type
  | S_empty_map of comparable_type * typ
  | S_map of stmt t
  | S_iter of stmt t
  | S_mem
  | S_get
  | S_update
  | S_loop of stmt t
  | S_loop_left of stmt t
  | S_lambda of typ * typ * stmt t
  | S_exec
  | S_dip of stmt t
  | S_failwith of expr t
  | S_cast
  | S_rename
  | S_concat
  | S_slice
  | S_pack
  | S_unpack
  | S_add
  | S_sub
  | S_mul
  | S_ediv
  | S_abs
  | S_neg
  | S_lsl
  | S_lsr
  | S_or
  | S_and
  | S_xor
  | S_not
  | S_compare
  | S_eq
  | S_neq
  | S_lt
  | S_gt
  | S_le
  | S_ge
  | S_self
  | S_contract of typ
  | S_transfer_tokens
  | S_set_delegate
  | S_create_account
  | S_create_contract of stmt t
  | S_implicit_account
  | S_now
  | S_amount
  | S_balance
  | S_check_signature
  | S_blake2b
  | S_sha256
  | S_sha512
  | S_hash_key
  | S_steps_to_quota
  | S_source
  | S_sender
  | S_address
  | S_todo

and _ node_data =
  | Stmt : stmt -> stmt node_data
  | Decl : decl -> decl node_data
  | Expr : expr -> expr node_data
  | Type : typ -> typ node_data
  | Comparable_type : comparable_type -> comparable_type node_data

and 'a t = { id : int; loc : Michelson.Location.t; data : 'a node_data }

let counter = ref (-1)

let next_counter () =
  let () = counter := !counter + 1 in
  !counter

let create ?(loc = Michelson.Location.Unknown) data =
  { id = next_counter (); loc; data }

let get_node_data : type a. a t -> a =
 fun n ->
  match n.data with
  | Stmt s -> s
  | Decl d -> d
  | Expr e -> e
  | Type t -> t
  | Comparable_type t -> t

(* let rec stmt_to_string = 
  let open Printf in
  function
  | Cfg_var_decl v ->
      sprintf "var %s" (get_node_data v)
  | Cfg_assign (lv, rv) ->
      sprintf "%s = %s" (to_string lv) (to_string rv)
  | Cfg_guard e ->
      sprintf "test %s" (to_string e)
  | Cfg_jump ->
      sprintf "jump"
  | Cfg_call (f, args) ->
      sprintf "%s (%s)" (to_string f)
        (sprint_list ~first:"" ~last:"" ~sep:", " to_string args) *)
let rec expr_to_string (_ : expr) = "" (* TODO: *)

and stmt_to_string (_ : stmt) = "" (* TODO: *)

and to_string : type a. a t -> string =
 fun n ->
  match n.data with
  | Stmt _ -> stmt_to_string (get_node_data n)
  | Decl d -> d
  | Expr e -> expr_to_string e
  | Type _ | Comparable_type _ -> ""

(* TODO: *)

type program = stmt t
