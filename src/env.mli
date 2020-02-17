type env = Failed | Stack of string Functional_stack.t

val next_var : Z.t ref -> string

val empty_env : env

val failed_env : env

val push : string -> env -> env

val pop : env -> string * env

val drop : env -> env

val peek : env -> string

val swap : env -> env

val dig : env -> Z.t -> env

val dug : env -> Z.t -> env

val dip : env -> Z.t -> string list * env

val dup : env -> string * env
