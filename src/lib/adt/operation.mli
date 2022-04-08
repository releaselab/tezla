open Core

type var = Var.t

type t =
  | O_create_contract of
      (Common_adt.Loc.t, Common_adt.Annot.t list) Carthage_adt.Adt.program
      * var
      * var
      * var
  | O_transfer_tokens of var * var * var
  | O_set_delegate of var
  | O_create_account of var * var * var * var

include Comparable.S with type t := t
include Sexpable.S with type t := t

val to_string : t -> string
