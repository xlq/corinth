type loc = Lexing.position
type dotted_name = string list

type sym_kind =
    | Undefined
    | Unit
    | Variable
    | Subprogram
    | Parameter

type symbol = {
    sym_parent: symbol;
    mutable sym_kind: sym_kind;
    sym_name: string;
    sym_first_seen: loc;
    mutable sym_defined: loc option;
    mutable sym_type: ttype option;
    mutable sym_locals: symbol list;
    mutable sym_parameters: symbol list;
    mutable sym_param_mode: param_mode;
}

and param_mode = Const_param | Var_param | Out_param

and ttype =
    | Integer_type  (* This is temporary, for development *)
    | Named_type of symbol

val new_root_symbol : unit -> symbol

val find_or_create_sym : symbol -> loc -> string -> symbol
val create_sym : symbol -> loc -> string -> sym_kind -> symbol
