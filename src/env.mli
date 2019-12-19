type env

val next_var : unit -> string

val empty_env : env

val failed_env : env

val push : string -> env -> env

val pop : env -> string * env

val drop : env -> env

val peek : env -> string

val swap : env -> env

val dig : env -> Z.t -> env

val dug : env -> Z.t -> env

val dip : env -> Z.t -> env * env

val dup : env -> string * env
