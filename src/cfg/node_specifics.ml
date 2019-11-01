open Batteries

module Make(N : Cfg_node.S) = struct
  open N

  let free_variables free_variables blocks =
    let open N in
    let open Set.Infix in
    let aux n acc = match get_node_data n with
        Cfg_assign (_, e)
      | Cfg_guard e -> acc ||. free_variables (get_node_data e)
      | Cfg_call (f, args) ->
          let f_fr = free_variables (get_node_data f) in
          List.fold_left (fun acc x ->
            acc ||. free_variables (get_node_data x)) (acc ||. f_fr) args
      | Cfg_jump | Cfg_var_decl _ -> Set.empty
    in Set.fold aux blocks Set.empty

  let find_assignments blocks x =
    let open N in
    let aux b acc = match get_node_data b with
        Cfg_assign (lv, _) when lv.id = x.id -> Set.add b acc
      | Cfg_assign _ | Cfg_call _ | Cfg_guard _ | Cfg_jump | Cfg_var_decl _ ->
          acc in
    Set.fold aux blocks Set.empty

  let aexp get_non_trivial_subexpr n =
    let open Set.Infix in
    match get_node_data n with
      Cfg_assign (_, rv) -> get_non_trivial_subexpr (get_node_data rv)
    | Cfg_guard e -> get_non_trivial_subexpr (get_node_data e)
    | Cfg_call (f, args) ->
        let f' = get_non_trivial_subexpr (get_node_data f) in
        List.fold_left (fun acc e ->
          acc ||. get_non_trivial_subexpr (get_node_data e)) f' args
    | Cfg_jump | Cfg_var_decl _ -> Set.empty

end
