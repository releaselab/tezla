open Format
open Adt

let simple_comparable_type ppf =
  let open Michelson.Adt in
  function
  | T_int -> fprintf ppf "int"
  | T_nat -> fprintf ppf "nat"
  | T_string -> fprintf ppf "string"
  | T_bytes -> fprintf ppf "bytes"
  | T_mutez -> fprintf ppf "mutez"
  | T_bool -> fprintf ppf "bool"
  | T_key_hash -> fprintf ppf "key_hash"
  | T_timestamp -> fprintf ppf "timestamp"
  | T_address -> fprintf ppf "address"

let rec comparable_type ppf =
  let open Michelson.Adt in
  function
  | T_simple_comparable_type t -> fprintf ppf "%a" simple_comparable_type t
  | T_comparable_pair (t_1, t_2) ->
      fprintf ppf "(pair %a %a)" simple_comparable_type (fst t_1)
        comparable_type (fst t_2)

let rec typ ppf =
  let open Michelson.Adt in
  function
  | T_comparable t -> fprintf ppf "%a" comparable_type t
  | T_key -> fprintf ppf "key"
  | T_unit -> fprintf ppf "unit"
  | T_signature -> fprintf ppf "signature"
  | T_option t -> fprintf ppf "option %a" typ (fst t)
  | T_list t -> fprintf ppf "list %a" typ (fst t)
  | T_set t -> fprintf ppf "%a" comparable_type (fst t)
  | T_operation -> fprintf ppf "operation"
  | T_contract t -> fprintf ppf "(contract %a)" typ (fst t)
  | T_pair (t_1, t_2) -> fprintf ppf "(pair %a %a)" typ (fst t_1) typ (fst t_2)
  | T_or (t_1, t_2) -> fprintf ppf "(or  %a %a)" typ (fst t_1) typ (fst t_2)
  | T_lambda (t_1, t_2) ->
      fprintf ppf "(lambda %a %a)" typ (fst t_1) typ (fst t_2)
  | T_map (t_1, t_2) ->
      fprintf ppf "(map %a %a)" comparable_type (fst t_1) typ (fst t_2)
  | T_big_map (t_1, t_2) ->
      fprintf ppf "(big_map %a %a)" comparable_type (fst t_1) typ (fst t_2)
  | T_chain_id -> fprintf ppf "chain_id"

let rec expr ppf = function
  | E_car e -> fprintf ppf "CAR %a" expr e
  | E_cdr e -> fprintf ppf "CDR %a" expr e
  | E_abs e -> fprintf ppf "ABS %a" expr e
  | E_neg e -> fprintf ppf "NEG %a" expr e
  | E_not e -> fprintf ppf "NOT %a" expr e
  | E_eq e -> fprintf ppf "EQ %a" expr e
  | E_neq e -> fprintf ppf "NEQ %a" expr e
  | E_lt e -> fprintf ppf "LT %a" expr e
  | E_gt e -> fprintf ppf "GT %a" expr e
  | E_leq e -> fprintf ppf "LEQ %a" expr e
  | E_geq e -> fprintf ppf "GEQ %a" expr e
  | E_left e -> fprintf ppf "LEFT %a" expr e
  | E_right e -> fprintf ppf "RIGHT %a" expr e
  | E_some e -> fprintf ppf "SOME %a" expr e
  | E_cast e -> fprintf ppf "CAST %a" expr e
  | E_pack e -> fprintf ppf "PACK %a" expr e
  | E_contract_of_address e -> fprintf ppf "CONTRACT %a" expr e
  | E_implicit_account e -> fprintf ppf "IMPLICIT_ACCOUNT %a" expr e
  | E_blake2b e -> fprintf ppf "BLAKE2B %a" expr e
  | E_sha256 e -> fprintf ppf "SHA256 %a" expr e
  | E_sha512 e -> fprintf ppf "SHA512 %a" expr e
  | E_hash_key e -> fprintf ppf "HASH_KEY %a" expr e
  | E_ident s
  | E_string s
  | E_timestamp s
  | E_signature s
  | E_key s
  | E_key_hash s
  | E_bytes s ->
      fprintf ppf "%s" s
  | E_int n | E_nat n | E_mutez n -> fprintf ppf "%a" Z.pp_print n
  | E_unit -> fprintf ppf "()"
  | E_bool b ->
      fprintf ppf "%a"
        (fun ppf -> function true -> fprintf ppf "True"
          | false -> fprintf ppf "False")
        b
  | E_none t -> fprintf ppf "NONE %a" typ (fst t)
  | E_add (e_1, e_2) -> fprintf ppf "ADD %a %a" expr e_1 expr e_2
  | E_sub (e_1, e_2) -> fprintf ppf "SUB %a %a" expr e_1 expr e_2
  | E_mul (e_1, e_2) -> fprintf ppf "MUL %a %a" expr e_1 expr e_2
  | E_div (e_1, e_2) -> fprintf ppf "EDIV %a %a" expr e_1 expr e_2
  | E_shiftL (e_1, e_2) -> fprintf ppf "LSL %a %a" expr e_1 expr e_2
  | E_shiftR (e_1, e_2) -> fprintf ppf "LSR %a %a" expr e_1 expr e_2
  | E_and (e_1, e_2) -> fprintf ppf "AND %a %a" expr e_1 expr e_2
  | E_or (e_1, e_2) -> fprintf ppf "OR %a %a" expr e_1 expr e_2
  | E_xor (e_1, e_2) -> fprintf ppf "XOR %a %a" expr e_1 expr e_2
  | E_compare (e_1, e_2) -> fprintf ppf "COMPARE %a %a" expr e_1 expr e_2
  | E_cons (e_1, e_2) -> fprintf ppf "CONS %a %a" expr e_1 expr e_2
  | E_pair (e_1, e_2) -> fprintf ppf "PAIR %a %a" expr e_1 expr e_2
  | E_mem (e_1, e_2) -> fprintf ppf "MEM %a %a" expr e_1 expr e_2
  | E_get (e_1, e_2) -> fprintf ppf "GET %a %a" expr e_1 expr e_2
  | E_concat (e_1, e_2) -> fprintf ppf "CONCAT %a %a" expr e_1 expr e_2
  | E_list (_, l) | E_set l ->
      pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "; ") expr ppf l
  | E_map l | E_big_map l ->
      let print_elem ppf (k, v) = fprintf ppf "Elt %a %a" expr k expr v in
      pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "; ") print_elem ppf l
  | E_update (e_1, e_2, e_3) ->
      fprintf ppf "UPDATE %a %a %a" expr e_1 expr e_2 expr e_3
  | E_slice (e_1, e_2, e_3) ->
      fprintf ppf "SLICE %a %a %a" expr e_1 expr e_2 expr e_3
  | E_check_signature (e_1, e_2, e_3) ->
      fprintf ppf "CHECK_SIGNATURE %a %a %a" expr e_1 expr e_2 expr e_3
  | E_unpack (t, e) -> fprintf ppf "UNPACK %a %a" typ (fst t) expr e
  | E_self -> fprintf ppf "SELF"
  | E_now -> fprintf ppf "NOW"
  | E_amount -> fprintf ppf "AMOUNT"
  | E_balance -> fprintf ppf "BALANCE"
  | E_steps_to_quota -> fprintf ppf "STEPS_TO_QUOTA"
  | E_source -> fprintf ppf "SOURCE"
  | E_sender -> fprintf ppf "SENDER"
  | E_address_of_contract e -> fprintf ppf "ADDRESS %a" expr e
  | E_size e -> fprintf ppf "SIZE %a" expr e
  | E_lift_option e -> fprintf ppf "lift_option %a" expr e
  | E_lift_or e -> fprintf ppf "lift_or %a" expr e
  | E_list_hd e -> fprintf ppf "list_hd %a" expr e
  | E_list_tl e -> fprintf ppf "list_tl %a" expr e
  | E_isnat e -> fprintf ppf "ISNAT %a" expr e
  | E_int_of_nat e -> fprintf ppf "INT %a" expr e
  | E_chain_id -> fprintf ppf "CHAIN_ID"
  | E_lambda (t_1, t_2, _) ->
      fprintf ppf "LAMBDA %a %a {...}" typ (fst t_1) typ (fst t_2)
  | E_exec (e_1, e_2) -> fprintf ppf "EXEC %s %s" e_1 e_2
  | E_create_contract_address _ -> (* TODO: *) fprintf ppf ""
  | E_create_account_address _ -> (* TODO: *) fprintf ppf ""
  | E_operation _ -> (* TODO: *) fprintf ppf ""

let rec stmt i ppf = function
  | S_seq (s_1, s_2) ->
      fprintf ppf "@[<%d>%a;]@\n%a" i (stmt i) s_1 (stmt i) s_2
  | S_var_decl s -> fprintf ppf "var %s" s
  | S_assign (s, e, t) -> (
      match t with
      | None -> fprintf ppf "var %s := %a" s expr e
      | Some t -> fprintf ppf "var %s : %a := %a" s typ (fst t) expr e )
  | S_skip -> fprintf ppf ""
  | S_drop s -> fprintf ppf "DROP %s" s
  | S_swap -> fprintf ppf "SWAP"
  | S_if (s, s_1, s_2) ->
      let i' = i + 1 in
      fprintf ppf "IF %s\n{\n@[<%d>%a]@\n}\n{\n@[<%d>%a]@\n}" s i' (stmt i') s_1
        i' (stmt i') s_2
  | S_if_none (s, s_1, s_2, _) ->
      let i' = i + 1 in
      fprintf ppf "IF_NONE %s\n{\n@[<%d>%a]@\n}\n{\n@[<%d>%a]@\n}" s i'
        (stmt i') s_1 i' (stmt i') s_2
  | S_if_left (s, s_1, s_2, _) ->
      let i' = i + 1 in
      fprintf ppf "IF_LEFT %s\n{\n@[<%d>%a]@\n}\n{\n@[<%d>%a]@\n}" s i'
        (stmt i') s_1 i' (stmt i') s_2
  | S_if_cons (s, s_1, _, _, s_2) ->
      let i' = i + 1 in
      fprintf ppf "IF_CONS %s\n{\n@[<%d>%a]@\n}\n{\n@[<%d>%a]@\n}" s i'
        (stmt i') s_1 i' (stmt i') s_2
  | S_loop (s, b) ->
      let i' = i + 1 in
      fprintf ppf "LOOP %s\n{\n@[<%d>%a]@\n}" s i' (stmt i') b
  | S_loop_left (s, b) ->
      let i' = i + 1 in
      fprintf ppf "LOOP_LEFT %s\n{\n@[<%d>%a]@\n}" s i' (stmt i') b
  | S_map (s, b) ->
      let i' = i + 1 in
      fprintf ppf "MAP %s\n{\n@[<%d>%a]@\n}" s i' (stmt i') b
  | S_iter (s, b) ->
      let i' = i + 1 in
      fprintf ppf "ITER %s\n{\n@[<%d>%a]@\n}" s i' (stmt i') b
  | S_failwith s -> fprintf ppf "FAILWITH %s" s
  | S_cast -> fprintf ppf "CAST"
  | S_contract t -> fprintf ppf "CONTRACT %a" typ (fst t)

let func ppf (b, v) = fprintf ppf "@[<1>%s => {\n%a\n}]@" v (stmt 2) b

let program ppf (_, _, b) = func ppf b
