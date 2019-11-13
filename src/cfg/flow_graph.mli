open Tezla

module Cfg :
  Sig.Flow_graph
    with type vertex = Ast.stmt Ast.t
     and type expr = Ast.expr
     and type program = Michelson.Ast.program

(* module Make_inter_cfg
    (F : Sig.Flow
           with type block = Ast.stmt
            and type vertex = Ast.stmt Ast.t) :
  Sig.Inter_flow_graph
    with type vertex = Ast.stmt Ast.t
     and type expr = Ast.expr *)
