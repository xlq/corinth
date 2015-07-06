type state

val new_state : Symtab.symbol -> state
val translate : state -> Symtab.symbol -> unit
