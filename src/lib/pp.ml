open Batteries
open Printf
open Adt

let string_of_typ = Michelson.Pp.string_of_typ

let string_of_data = Michelson.Pp.string_of_data

let string_of_var v = v.var_name

let string_of_operation =
  let open Printf in
  function
  | O_create_account (v_1, v_2, v_3, v_4) ->
      sprintf "CREATE_ACCOUNT %s %s %s %s" v_1.var_name v_2.var_name
        v_3.var_name v_4.var_name
  | O_create_contract (_, v_1, v_2, v_3) ->
      sprintf "CREATE_CONTRACT {...} %s %s %s" v_1.var_name v_2.var_name
        v_3.var_name
  | O_set_delegate e -> sprintf "SET_DELEGATE %s" (string_of_var e)
  | O_transfer_tokens (v_1, v_2, v_3) ->
      sprintf "TRANSFER_TOKENS %s %s %s" v_1.var_name v_2.var_name v_3.var_name

let string_of_expr = function
  | E_push (d, t) -> sprintf "PUSH %s %s" (string_of_typ t) (string_of_data d)
  | E_car e -> sprintf "CAR %s" (string_of_var e)
  | E_cdr e -> sprintf "CDR %s" (string_of_var e)
  | E_abs e -> sprintf "ABS %s" (string_of_var e)
  | E_neg e -> sprintf "NEG %s" (string_of_var e)
  | E_not e -> sprintf "NOT %s" (string_of_var e)
  | E_eq e -> sprintf "EQ %s" (string_of_var e)
  | E_neq e -> sprintf "NEQ %s" (string_of_var e)
  | E_lt e -> sprintf "LT %s" (string_of_var e)
  | E_gt e -> sprintf "GT %s" (string_of_var e)
  | E_leq e -> sprintf "LEQ %s" (string_of_var e)
  | E_geq e -> sprintf "GEQ %s" (string_of_var e)
  | E_left (e, t) -> sprintf "LEFT %s %s" (string_of_typ t) (string_of_var e)
  | E_right (e, t) -> sprintf "RIGHT %s %s" (string_of_typ t) (string_of_var e)
  | E_some e -> sprintf "SOME %s" (string_of_var e)
  | E_pack e -> sprintf "PACK %s" (string_of_var e)
  | E_implicit_account e -> sprintf "IMPLICIT_ACCOUNT %s" (string_of_var e)
  | E_blake2b e -> sprintf "BLAKE2B %s" (string_of_var e)
  | E_sha256 e -> sprintf "SHA256 %s" (string_of_var e)
  | E_sha512 e -> sprintf "SHA512 %s" (string_of_var e)
  | E_hash_key e -> sprintf "HASH_KEY %s" (string_of_var e)
  | E_unit -> sprintf "UNIT"
  | E_none t -> sprintf "NONE %s" (string_of_typ t)
  | E_add (v_1, v_2) -> sprintf "ADD %s %s" v_1.var_name v_2.var_name
  | E_sub (v_1, v_2) -> sprintf "SUB %s %s" v_1.var_name v_2.var_name
  | E_mul (v_1, v_2) -> sprintf "MUL %s %s" v_1.var_name v_2.var_name
  | E_div (v_1, v_2) -> sprintf "EDIV %s %s" v_1.var_name v_2.var_name
  | E_shiftL (v_1, v_2) -> sprintf "LSL %s %s" v_1.var_name v_2.var_name
  | E_shiftR (v_1, v_2) -> sprintf "LSR %s %s" v_1.var_name v_2.var_name
  | E_and (v_1, v_2) -> sprintf "AND %s %s" v_1.var_name v_2.var_name
  | E_or (v_1, v_2) -> sprintf "OR %s %s" v_1.var_name v_2.var_name
  | E_xor (v_1, v_2) -> sprintf "XOR %s %s" v_1.var_name v_2.var_name
  | E_compare (v_1, v_2) -> sprintf "COMPARE %s %s" v_1.var_name v_2.var_name
  | E_cons (v_1, v_2) -> sprintf "CONS %s %s" v_1.var_name v_2.var_name
  | E_pair (v_1, v_2) -> sprintf "PAIR %s %s" v_1.var_name v_2.var_name
  | E_mem (v_1, v_2) -> sprintf "MEM %s %s" v_1.var_name v_2.var_name
  | E_get (v_1, v_2) -> sprintf "GET %s %s" v_1.var_name v_2.var_name
  | E_concat (v_1, v_2) -> sprintf "CONCAT %s %s" v_1.var_name v_2.var_name
  | E_concat_list e -> sprintf "CONCAT %s" (string_of_var e)
  | E_update (v_1, v_2, v_3) ->
      sprintf "UPDATE %s %s %s" v_1.var_name v_2.var_name v_3.var_name
  | E_slice (v_1, v_2, v_3) ->
      sprintf "SLICE %s %s %s" v_1.var_name v_2.var_name v_3.var_name
  | E_check_signature (v_1, v_2, v_3) ->
      sprintf "CHECK_SIGNATURE %s %s %s" v_1.var_name v_2.var_name v_3.var_name
  | E_unpack (t, v) -> sprintf "UNPACK %s %s" (string_of_typ t) v.var_name
  | E_self -> sprintf "SELF"
  | E_now -> sprintf "NOW"
  | E_amount -> sprintf "AMOUNT"
  | E_balance -> sprintf "BALANCE"
  | E_source -> sprintf "SOURCE"
  | E_sender -> sprintf "SENDER"
  | E_address_of_contract e -> sprintf "ADDRESS %s" (string_of_var e)
  | E_size e -> sprintf "SIZE %s" (string_of_var e)
  | E_unlift_option e -> sprintf "unlift_option %s" (string_of_var e)
  | E_unlift_or_left e -> sprintf "unlift_or_left %s" (string_of_var e)
  | E_unlift_or_right e -> sprintf "unlift_or_right %s" (string_of_var e)
  | E_hd e -> sprintf "hd %s" (string_of_var e)
  | E_tl e -> sprintf "tl %s" (string_of_var e)
  | E_isnat e -> sprintf "ISNAT %s" (string_of_var e)
  | E_int_of_nat e -> sprintf "INT %s" (string_of_var e)
  | E_chain_id -> sprintf "CHAIN_ID"
  | E_lambda (t_1, t_2, _) ->
      sprintf "LAMBDA %s %s {...}" (string_of_typ t_1) (string_of_typ t_2)
  | E_exec (v_1, v_2) -> sprintf "EXEC %s %s" v_1.var_name v_2.var_name
  | E_contract_of_address (t, v) ->
      sprintf "CONTRACT %s %s" (string_of_typ t) v.var_name
  | E_create_contract_address _ -> (* TODO: *) sprintf "CREATE_CONTRACT_address"
  | E_operation o -> string_of_operation o
  | E_dup v -> sprintf "DUP %s" v.var_name
  | E_nil t -> sprintf "NIL %s" (string_of_typ t)
  | E_empty_set t -> sprintf "EMPTY_SET %s" (string_of_typ t)
  | E_empty_map (t_k, t_v) ->
      sprintf "EMPTY_MAP %s %s" (string_of_typ t_k) (string_of_typ t_v)
  | E_empty_big_map (t_k, t_v) ->
      sprintf "EMPTY_BIG_MAP %s %s" (string_of_typ t_k) (string_of_typ t_v)
  | E_apply (v_1, v_2) -> sprintf "APPLY %s %s" v_1.var_name v_2.var_name
  | E_append (v_1, v_2) -> sprintf "append(%s, %s)" v_1.var_name v_2.var_name
  | E_phi (v_1, v_2) -> sprintf "phi(%s, %s)" v_1.var_name v_2.var_name
  | E_special_nil_list _ -> sprintf "[]"

let string_of_list f l =
  let open Printf in
  let values =
    let rec aux acc = function
      | [] -> ""
      | h :: tl ->
          aux
            ( if String.length acc > 0 then sprintf "%s; %s" acc (f h)
            else sprintf "%s" (f h) )
            tl
    in
    aux "" l
  in
  "[ " ^ values ^ " ]"

let rec print_stmt i ch n =
  match n.stm with
  | S_seq ({ id = _; stm = S_skip }, s) | S_seq (s, { id = _; stm = S_skip }) ->
      print_stmt i ch s
  | S_seq (s_1, s_2) ->
      fprintf ch "%a;\n%a" (print_stmt i) s_1 (print_stmt i) s_2
  | S_assign (v, e) -> fprintf ch "%s := %s" v.var_name (string_of_expr e)
  | S_skip -> fprintf ch ""
  | S_drop l -> fprintf ch "DROP %s" (string_of_list (fun x -> x.var_name) l)
  | S_swap -> fprintf ch "SWAP"
  | S_dig -> fprintf ch "DIG"
  | S_dug -> fprintf ch "DUG"
  | S_if (v, s_1, s_2) ->
      let i' = i + 1 in
      fprintf ch "IF %s\n{\n%a\n}\n{\n%a\n}" v.var_name (print_stmt i') s_1
        (print_stmt i') s_2
  | S_if_none (v, s_1, s_2) ->
      let i' = i + 1 in
      fprintf ch "IF_NONE %s\n{\n%a\n}\n{\n%a\n}" v.var_name (print_stmt i') s_1
        (print_stmt i') s_2
  | S_if_left (v, s_1, s_2) ->
      let i' = i + 1 in
      fprintf ch "IF_LEFT %s\n{\n%a\n}\n{\n%a\n}" v.var_name (print_stmt i') s_1
        (print_stmt i') s_2
  | S_if_cons (v, s_1, s_2) ->
      let i' = i + 1 in
      fprintf ch "IF_CONS %s\n{\n%a\n}\n{\n%a\n}" v.var_name (print_stmt i') s_1
        (print_stmt i') s_2
  | S_loop (v, (v_1, v_2), b) ->
      let i' = i + 1 in
      fprintf ch "LOOP %s := phi(%s, %s)\n{\n%a\n}" v.var_name v_1.var_name
        v_2.var_name (print_stmt i') b
  | S_loop_left (v, (v_1, v_2), b) ->
      let i' = i + 1 in
      fprintf ch "LOOP_LEFT %s := phi(%s, %s)\n{\n%a\n}" v.var_name v_1.var_name
        v_2.var_name (print_stmt i') b
  | S_map ((c, (c_1, c_2)), (r, (r_1, r_2)), b) ->
      let i' = i + 1 in
      fprintf ch "MAP %s := phi(%s, %s) with %s := phi(%s, %s)\n{\n%a\n}"
        c.var_name c_1.var_name c_2.var_name r.var_name r_1.var_name
        r_2.var_name (print_stmt i') b
  | S_iter (v, (v_1, v_2), b) ->
      let i' = i + 1 in
      fprintf ch "ITER %s := phi(%s, %s)\n{\n%a\n}" v.var_name v_1.var_name
        v_2.var_name (print_stmt i') b
  | S_failwith v -> fprintf ch "FAILWITH %s" v.var_name

let func ppf (b, v) = fprintf ppf "@[<1>%s => {\n%a\n}" v (print_stmt 2) b

let program ppf (_, _, b) = func ppf b
