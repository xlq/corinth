(* comma_concat "and" [a;b;c] -> "a, b and c" *)
val comma_concat : string -> string list -> string

val unsome : 'a option -> 'a

val times : int -> string -> string

val maybe_find : ('a -> bool) -> 'a list -> 'a option
