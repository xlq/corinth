open Big_int

type loc = Lexing.position
type dotted_name = string list

type binop = Add | Subtract | Multiply | Divide | LT | GT | LE | GE | EQ | NE

type sym_kind =
    | Unit
    | Var (* variable or field *)
    | Proc
    | Type_sym
    | Type_param
    | Param
    | Const

type symbol = {
    sym_parent: symbol; (* Parent symbol (this symbol is in sym_parent.sym_locals). *)
    sym_kind: sym_kind;
    sym_name: string;
    mutable sym_defined: loc option; (* Can be None for parent units that aren't loaded/defined. *)
    (* Var | Param -> sym_type is the type of the variable/parameter.
       Proc -> sym_type is the return type of the procedure.
       Type_sym -> sym_type is the definition of the type.
       Type_param -> sym_type is what the type parameter is currently unified with. *)
    mutable sym_type: ttype option;
    mutable sym_locals: symbol list; (* Sub-symbols. Order is important for parameters. *)
    mutable sym_dispatching: bool; (* Parameter is dispatching (declared "disp") *)
    mutable sym_param_mode: param_mode;
    mutable sym_code: istmt list option;
    mutable sym_imported: bool;
    mutable sym_const: iexpr option;
    mutable sym_selected: bool;
    mutable sym_translated: bool; (* Body has been translated?
        If false, some children may be missing. *)
    mutable sym_backend_translated: bool;
}

and param_mode = Const_param | Var_param | Out_param

and ttype =
    | No_type
    | Boolean_type
    | Integer_type  (* This is temporary, for development *)
    | Char_type
    | Named_type of symbol * (symbol * ttype) list
    | Pointer_type of ttype
    | Record_type of symbol option
    | Proc_type of symbol

and istmt =
    | Call of loc * iexpr * (symbol * iexpr) list
    | Assign of loc * iexpr * iexpr
    | Return of loc * iexpr option
    | If_stmt of (loc * iexpr * istmt list) list * (loc * istmt list) option
    | While_stmt of loc * iexpr * istmt list

and iexpr =
    | Name of loc * symbol
    | Int_literal of loc * big_int
    | String_literal of loc * string
    | Apply of loc * iexpr * (symbol * iexpr) list
    | Record_cons of loc * symbol (* record type *) * (symbol * iexpr) list
    | Field_access of loc * iexpr * symbol
    | Binop of loc * iexpr * binop * iexpr

val new_root_sym : unit -> symbol
val describe_sym : symbol -> string (* for error messages *)
val create_sym : symbol -> loc -> string -> sym_kind -> symbol
val get_type_params : symbol -> symbol list
val get_fields : symbol -> symbol list (* get record fields, including from base type *)
val get_params : symbol -> symbol list (* get proc parameters *)
val string_of_type : ttype -> string
val sym_is_grandchild : symbol -> symbol -> bool
val full_name : symbol -> string
