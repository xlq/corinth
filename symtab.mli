type loc = Lexing.position
type dotted_name = string list

type sym_kind =
    | Unit
    | Var (* variable or field *)
    | Proc
    | Type_sym
    | Type_param
    | Param

type symbol = {
    sym_parent: symbol; (* Parent symbol (this symbol is in sym_parent.sym_locals). *)
    sym_kind: sym_kind;
    sym_name: string;
    mutable sym_defined: loc option; (* Can be None for parent units that aren't loaded/defined. *)
    mutable sym_type: ttype option; (* Type of variable/param, return type of function *)
    mutable sym_locals: symbol list; (* Sub-symbols. Order is important for parameters. *)
    mutable sym_dispatching: bool; (* Parameter is dispatching (declared "disp") *)
    mutable sym_param_mode: param_mode;
    mutable sym_code: istmt list option;
    mutable sym_selected: bool;
    mutable sym_translated: bool; (* Body has been translated?
        If false, some children may be missing. *)
    mutable sym_backend_translated: bool;
}

and param_mode = Const_param | Var_param | Out_param

and ttype =
    | No_type
    | Integer_type  (* This is temporary, for development *)
    | Named_type of symbol * (symbol * ttype) list
    | Pointer_type of ttype
    | Record_type of symbol option
    | Proc_type of symbol

and istmt =
    | Call of loc * iexpr * (symbol * iexpr) list

and iexpr =
    | Name of loc * symbol
    | Apply of loc * iexpr * (symbol * iexpr) list
    | Field_access of loc * iexpr * symbol

val new_root_sym : unit -> symbol
val describe_sym : symbol -> string (* for error messages *)
val create_sym : symbol -> loc -> string -> sym_kind -> symbol
val get_type_params : symbol -> symbol list
val get_fields : symbol -> symbol list (* get record fields, including from base type *)
val get_params : symbol -> symbol list (* get proc parameters *)
val string_of_type : ttype -> string
val sym_is_grandchild : symbol -> symbol -> bool
val full_name : symbol -> string
