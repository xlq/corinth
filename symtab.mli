type loc = Lexing.position
type dotted_name = string list

type sym_kind =
    | Unit
    | Variable
    | Subprogram
    | Parameter
    | Class_type

type symbol = {
    sym_parent: symbol;
    mutable sym_kind: sym_kind;
    sym_name: string;
    sym_first_seen: loc;
    mutable sym_defined: loc option;
    mutable sym_type: ttype option;
    mutable sym_locals: symbol list;
    mutable sym_param_mode: param_mode;
    mutable sym_base_class: symbol option;
    mutable sym_code: istmt list option;
}

and param_mode = Const_param | Var_param | Out_param

and ttype =
    | Integer_type  (* This is temporary, for development *)
    | Named_type of symbol

and istmt =
    | Assignment of loc * iexpr * iexpr

and iexpr =
    | Name of loc * symbol
    | Binop of loc * iexpr * binop * iexpr

and binop = Add | Subtract | Multiply | Divide

val new_root_symbol : unit -> symbol

val find_or_create_sym : symbol -> loc -> string -> sym_kind -> symbol
val create_sym : symbol -> loc -> string -> sym_kind -> symbol
val search_scope : symbol -> loc -> string -> sym_kind list -> string -> symbol
val search_for_dotted_name : symbol -> loc -> dotted_name -> sym_kind list -> string -> symbol
val parameters : symbol -> symbol list
