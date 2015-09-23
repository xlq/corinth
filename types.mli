open Symtab

type context

exception Type_mismatch

val new_context : unit -> context
val coerce : context -> ttype -> ttype -> unit
