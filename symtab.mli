open Big_int

type loc = Lexing.position
type dotted_name = string list

type binop = Add | Subtract | Multiply | Divide | LT | GT | LE | GE | EQ | NE

type sym_kind =
    | Unit
    | Var (* variable or field *)
    | Proc
    | Class
    | Class_proc
    | Type_sym
    | Type_param
    | Param
    | Const
    | Proc_type_sym (* Proc_type ttype points to this symbol kind for its parameters/return type etc. *)

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
    mutable sym_tconstraints: (symbol (* Class *) * tbinds) list; (* type parameter constraints *)
    mutable sym_implementations: symbol list; (* List of Proc for Class_proc symbol (XXX: SCOPING RULES!) *)
    mutable sym_param_mode: param_mode;
    mutable sym_code: istmt list option;
    mutable sym_imported: string option;
    mutable sym_abstract: bool;
    mutable sym_const: iexpr option; (* definition of constants *)
    mutable sym_selected: bool;
    mutable sym_translated: bool; (* Body has been translated?
        If false, some children may be missing. *)
    mutable sym_backend_translated: int;
}

and param_mode = Const_param | Var_param | Out_param

and ttype =
    | No_type
    | Boolean_type
    | Integer_type  (* This is temporary, for development *)
    | Char_type
    | Named_type of symbol * tbinds
    | Pointer_type of ttype
    | Record_type of symbol option
    | Proc_type of symbol * tbinds

and tbinds = (symbol * ttype) list

and istmt =
    | Call of loc * iexpr * (symbol * iexpr) list * tbinds
            * (symbol * (symbol * symbol) list) list ref
    | Assign of loc * iexpr * iexpr
    | Return of loc * iexpr option
    | If_stmt of (loc * iexpr * istmt list) list * (loc * istmt list) option
    | While_stmt of loc * iexpr * istmt list

and iexpr =
    | Name of loc * symbol
    | Int_literal of loc * big_int
    | String_literal of loc * string
    | Char_literal of loc * string
    | Dispatch of int (* index in sym_tconstraints *) * symbol * tbinds (* - XXX: needed? *)
    | Apply of loc * iexpr * (symbol * iexpr) list (* parameter bindings *)
                           * tbinds (* type parameter bindings (XXX: needed?) *)
                           * (symbol * (symbol * symbol) list) list ref (* classes *)
    | Record_cons of loc * symbol (* record type *) * (symbol * iexpr) list
    | Field_access of loc * iexpr * symbol
    | Binop of loc * iexpr * binop * iexpr
    | Deref of loc * iexpr
    | New of loc * ttype * iexpr

val is_kind : sym_kind -> symbol -> bool
val new_root_sym : unit -> symbol
val describe_sym : symbol -> string (* for error messages *)
val create_sym : symbol -> loc -> string -> sym_kind -> symbol
val get_type_params : symbol -> symbol list
val get_fields : symbol -> symbol list (* get record fields, including from base type *)
val get_params : symbol -> symbol list (* get proc parameters *)
val string_of_type : ttype -> string
val string_of_type_2 : tbinds -> ttype -> string
val sym_is_grandchild : symbol -> symbol -> bool
val full_name : symbol -> string
val iter_type_params_in : (symbol -> unit) -> ttype -> unit (* call function for each type parameter in type *)
