open Symtab

exception Internal_error
exception Compile_error
val string_of_location : Lexing.position -> string
val syntax_error : Lexing.position -> string -> unit
val semantic_error : Lexing.position -> string -> unit
val internal_error : Lexing.position -> string -> 'a
val type_error : Lexing.position -> Types.type_error -> unit
