module Make_cfg
    (F : Sig.Flow
           with type block = Cfg_node.stmt
            and type vertex = Cfg_node.stmt Cfg_node.t) :
  Sig.Flow_graph
    with type vertex = Cfg_node.stmt Cfg_node.t
     and type expr = Cfg_node.expr

module Make_inter_cfg
    (F : Sig.Flow
           with type block = Cfg_node.stmt
            and type vertex = Cfg_node.stmt Cfg_node.t) :
  Sig.Inter_flow_graph
    with type vertex = Cfg_node.stmt Cfg_node.t
     and type expr = Cfg_node.expr
