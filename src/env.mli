type 'a env = Failed | Stack of 'a list

val next_var : unit -> string

val empty_env : 'a env

val push : 'a -> 'a env -> 'a env

val pop : 'a env -> 'a * 'a env

val drop : 'a env -> 'a env

val peek : 'a env -> 'a

val swap : 'a env -> 'a env

val dig : 'a env -> Z.t -> 'a env

val dug : 'a env -> Z.t -> 'a env

val dip : 'a env -> Z.t -> 'a list * 'a env

val join : (string -> 'a) -> 'a env -> 'a env -> 'a env
