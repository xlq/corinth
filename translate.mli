type translation_state

val new_translation_state : Symtab.symbol -> translation_state
val trans_unit : translation_state -> Parse_tree.unit_decl -> unit
val finish_trans : translation_state -> unit
