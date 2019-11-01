open Michelscil
module N = Cfg_node

module Common = struct
  type program = Michelson_scil.stmt list

  type vertex = N.stmt N.t

  type expr = N.expr

  type edge_label = Normal | If_true | If_false

  module V = struct
    type t = vertex

    let compare x y = compare x.N.id y.N.id

    let hash x = Hashtbl.hash x.N.id

    let equal x y = x.N.id = y.N.id
  end

  module E = struct
    type t = edge_label

    let compare = compare

    let default = Normal

    (*let to_string = function
        Normal  -> ""
      | If_true   -> "true"
      | If_false    -> "false"*)
  end

  module G = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (V) (E)

  module Display (X : sig
    val label_to_subgraph : vertex -> Graph.Graphviz.DotAttributes.subgraph

    val label_to_dot_label : vertex -> string
  end) =
  struct
    include G

    let vertex_name v = string_of_int v.N.id

    let graph_attributes _ = []

    let default_vertex_attributes _ = [`Shape `Box; `Fontname "Courier"]

    let vertex_attributes v = [`Label (X.label_to_dot_label v)]

    let default_edge_attributes _ = []

    let edge_attributes _ = []

    let get_subgraph v = Some (X.label_to_subgraph v)
  end

  module Wrapper = struct
    let inflow g n = G.pred g n |> List.map (fun n -> n.N.id)

    let outflow g n = G.succ g n |> List.map (fun n -> n.N.id)

    let is_extremal exts l = List.mem l exts

    let add g p func_id v i =
      let () = Hashtbl.replace p i func_id in
      G.add_vertex g v

    let connect g label l l' = G.add_edge_e g (G.E.create l label l')

    let dot_output _ g p f =
      let module Helper = struct
        let label_to_dot_label n =
          Printf.sprintf "[%s]^%d" (N.to_string n) n.N.id

        let label_to_subgraph n =
          let fid = Hashtbl.find p n.N.id in
          { Graph.Graphviz.DotAttributes.sg_name= fid
          ; sg_attributes= [`Label fid]
          ; sg_parent= None }
      end in
      let module Dot_ = Graph.Graphviz.Dot (Display (Helper)) in
      let oc = open_out f in
      Dot_.output_graph oc g ; close_out oc

    let display_with_gv b g p =
      let tmp_dot = Filename.temp_file "graph" ".dot" in
      dot_output b g p tmp_dot ;
      let tmp_ps = Filename.temp_file "graph" ".ps" in
      ignore
        (Sys.command
           ( "dot -Tps " ^ tmp_dot ^ " > " ^ tmp_ps ^ "; evince " ^ tmp_ps
           ^ " &" )) ;
      Sys.remove tmp_dot
  end
end

module Make_cfg
    (F : Sig.Flow with type block = N.stmt and type vertex = Common.vertex) =
struct
  open Batteries
  include Common

  type t =
    { blocks: (int, vertex) Hashtbl.t
    ; flow: G.t
    ; functions: (int, string) Hashtbl.t
    ; mutable extremals: int list
    ; mutable extremalsR: int list }

  let create () =
    { blocks= Hashtbl.create 10
    ; flow= G.create ()
    ; functions= Hashtbl.create 10
    ; extremals= []
    ; extremalsR= [] }

  let get t = Hashtbl.find t.blocks

  let inflow g i =
    let n = get g i in
    Wrapper.inflow g.flow n

  let outflow g i =
    let n = get g i in
    Wrapper.outflow g.flow n

  let is_extremal g = Wrapper.is_extremal g.extremals

  let is_extremalR g = Wrapper.is_extremal g.extremalsR

  let add t func_id v =
    let () = Hashtbl.add t.blocks v.N.id v in
    Wrapper.add t.flow t.functions func_id v v.N.id

  let connect {flow= g; _} ?(label = E.default) = Wrapper.connect g label

  let get_blocks {blocks= b; _} = b

  let get_func_id {functions= p; _} = Hashtbl.find p

  let extremal t l = t.extremals <- l :: t.extremals

  let extremalR t l = t.extremalsR <- l :: t.extremalsR

  let labels {blocks; _} = Hashtbl.fold (fun l _ -> Set.add l) blocks Set.empty

  let dot_output {blocks= b; flow= g; functions= p; _} =
    Wrapper.dot_output b g p

  let display_with_gv {blocks= b; flow= g; functions= p; _} =
    Wrapper.display_with_gv b g p 

  let show = display_with_gv

  let generate_from_program p =
    let open Batteries in
    let graph = create () in
    let pBlocks = Hashtbl.create 10 in
    let env = Env.empty_env in
    let _, p_scil = Converter.convert env p in
    let add_edge (i, j) = connect graph i j in
    let rec aux = function
      | h_1 :: h_2 :: t ->
          let h_1_data = Sl.get_node_data h_1 in
          let n_1 = N.create ~loc:h_1.Sl.loc (Decl h_1_data) in
          let n_1' = N.create ~loc:h_1.Sl.loc (Stmt (Cfg_var_decl n_1)) in
          let h_2_data = Sl.get_node_data h_2 in
          let n_2 = N.create ~loc:h_2.Sl.loc (Decl h_2_data) in
          let n_2' = N.create ~loc:h_2.Sl.loc (Stmt (Cfg_var_decl n_2)) in
          let () = add_edge (n_1', n_2') in
          aux (h_2 :: t)
      | [h] ->
          let h_data = Sl.get_node_data h in
          let n = N.create ~loc:h.Sl.loc (Decl h_data) in
          let n' = N.create ~loc:h.Sl.loc (Stmt (Cfg_var_decl n)) in
          Some n'
      | [] ->
          None
    in
    let last_decl = aux global_decls in
    let () =
      List.iter
        (fun (f, _, b) ->
          let {F.correspondence= ht; initial; nodes; flow; _} = F.flow b in
          let () = Set.iter (fun b -> add graph f b) nodes in
          let init = Hashtbl.find ht (F.init b) in
          let () = extremal graph init.id in
          let finals = Set.map (Hashtbl.find ht) (F.final b) in
          let () = Set.iter (fun n -> extremal graph n.N.id) finals in
          let () = Hashtbl.replace pBlocks f nodes in
          let () =
            match last_decl with
            | Some l ->
                Set.iter (fun i -> add_edge (l, i)) initial
            | None ->
                ()
          in
          Set.iter add_edge flow)
        funcs
    in
    graph
end

module Make_inter_cfg
    (F : Sig.Flow
           with type block = Cfg_node.stmt
            and type vertex = Common.vertex) =
struct
  open Batteries
  include Common

  type t =
    { blocks: (int, vertex) Hashtbl.t
    ; flow: G.t
    ; functions: (int, string) Hashtbl.t
    ; mutable extremals: int list
    ; mutable extremalsR: int list
    ; mutable interflow: (int * int * int * int) list }

  let create () =
    { blocks= Hashtbl.create 10
    ; flow= G.create ()
    ; functions= Hashtbl.create 10
    ; extremals= []
    ; extremalsR= []
    ; interflow= [] }

  let get t = Hashtbl.find t.blocks

  let inflow g i =
    let n = get g i in
    Wrapper.inflow g.flow n

  let outflow g i =
    let n = get g i in
    Wrapper.outflow g.flow n

  let is_extremal g = Wrapper.is_extremal g.extremals

  let is_extremalR g = Wrapper.is_extremal g.extremalsR

  let add t func_id v =
    let () = Hashtbl.add t.blocks v.N.id v in
    Wrapper.add t.flow t.functions func_id v v.id

  let connect {flow= g; _} ?(label = E.default) = Wrapper.connect g label

  let get_blocks {blocks= b; _} = b

  let get_func_id {functions= p; _} = Hashtbl.find p

  let extremal t l = t.extremals <- l :: t.extremals

  let extremalR t l = t.extremalsR <- l :: t.extremalsR

  let labels {blocks; _} = Hashtbl.fold (fun l _ -> Set.add l) blocks Set.empty

  (*let interflow t l = t.interflow <- l::t.interflow*)
  let inter_flow t = t.interflow

  let dot_output {blocks= b; flow= g; functions= p; _} =
    Wrapper.dot_output b g p

  let display_with_gv {blocks= b; flow= g; functions= p; _} =
    Wrapper.display_with_gv b g p

  let show = display_with_gv

  let generate_from_program _ = (* TODO: *) create ()
end
