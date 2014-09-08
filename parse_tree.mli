open Symtab

type loc = Lexing.position
type dotted_name = string list

type 'a associative =
    'a list * (string * 'a) list

type unit_decl = loc * dotted_name * decl list

and decl =
    | Var_decl of loc * string list * ttype
    | Sub_decl of loc * string * parameter list * ttype option

and parameter = loc * param_mode * string list * ttype

and param_mode = Const_param | Var_param | Out_param

and ttype =
    | Integer (* This is temporary, for development. *)
    | Named_type of dotted_name
