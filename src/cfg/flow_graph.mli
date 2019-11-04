open Michelscil

module Cfg :
  Sig.Flow_graph
    with type vertex = Morley.stmt Morley.t
     and type expr = Morley.expr
     and type program = Michelson.instruction

(* module Make_inter_cfg
    (F : Sig.Flow
           with type block = Morley.stmt
            and type vertex = Morley.stmt Morley.t) :
  Sig.Inter_flow_graph
    with type vertex = Morley.stmt Morley.t
     and type expr = Morley.expr *)
