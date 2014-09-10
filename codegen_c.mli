type state

val new_state : unit -> state
val trans_sub : state -> Symtab.symbol -> unit
