open Big_int

type loc = Lexing.position
type dotted_name = string list

type binop = Add | Subtract | Multiply | Divide | LT | GT | LE | GE | EQ | NE | And | Or

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
    mutable sym_virtual: bool;
    mutable sym_abstract: bool;
    mutable sym_implementations: symbol list; (* List of Proc for virtual Proc symbol (XXX: SCOPING RULES!) *)
    mutable sym_param_mode: param_mode;
    mutable sym_code: istmt list option;
    mutable sym_imported: string option;
    mutable sym_const: iexpr option; (* definition of constants *)
    mutable sym_selected: bool;
    mutable sym_translated: bool; (* Body has been translated?
        If false, some children may be missing. *)
    mutable sym_backend_translated: int;
}

(* Note: parameters are stored in two places:
   1. As children of Proc symbols. This represents the parameters within the proc.
   2. As part of the TProc type. This represents the type of the proc. *)
and param_mode = Const_param | Var_param | Out_param

and ttype =
    | TNone
    | TBoolean
    | TInteger
    | TChar
    | TName of symbol
    | TVar of tvar
    | TPointer of ttype
    | TRecord of record_type
    | TProc of proc_type
    | TEnum of symbol list (* Const symbols that constitute the enumeration *)
    | TUniv of tvar * ttype

and tvar = {
    tvar_origin: symbol option; (* originally came from this symbol *)
    tvar_id: int; (* unique id for dumping *)
    mutable tvar_link: ttype option; (* type substitution *)
}

and record_type = {
    rec_loc: loc;
    rec_fields: record_field list;
}

and record_field = {
    field_loc: loc;
    field_name: string;
    field_type: ttype;
}

and proc_type = {
    proc_loc: loc;
    proc_params: proc_param list;
    proc_return: ttype;
}

and proc_param = {
    param_loc: loc;
    mutable param_mode: param_mode;
    param_name: string option;
    param_type: ttype;
}

and tbinds = (symbol * ttype) list

and classarg = (* what to pass to proc to satisfy classes *)
    | Implement of symbol * (symbol * symbol) list
    | Forward of int (* index into caller's tconstraints (XXX: ugly) *)

and istmt =
    | Call of loc * iexpr * (proc_param * iexpr) list
    | Assign of loc * iexpr * iexpr
    | Return of loc * iexpr option
    | If_stmt of (loc * iexpr * istmt list) list * (loc * istmt list) option
    | While_stmt of loc * iexpr * istmt list

and iexpr =
    | Name of loc * symbol
    | Bool_literal of loc * bool
    | Int_literal of loc * big_int
    | String_literal of loc * string
    | Char_literal of loc * string
    | Dispatch of int (* index in sym_tconstraints *) * symbol * tbinds (* - XXX: needed? *)
    | Apply of loc * iexpr * (proc_param * iexpr) list (* parameter bindings *)
    | Record_cons of loc * ttype (* record type *) * (string * iexpr) list
    | Field_access of loc * iexpr * string
    | Binop of loc * iexpr * binop * iexpr
    | Deref of loc * iexpr
    | Not of loc * iexpr
    | New of loc * ttype * iexpr
    | Bind of ttype * iexpr (* bind type parameter *)

val new_tvar : symbol option -> tvar
val is_kind : sym_kind -> symbol -> bool
val new_root_sym : unit -> symbol
val describe_sym : symbol -> string (* for error messages *)
val create_sym : symbol -> loc -> string -> sym_kind -> symbol
val get_type_params : symbol -> symbol list
val get_params : symbol -> symbol list
val string_of_tvar : tvar -> string
val string_of_type : ttype -> string
val sym_is_grandchild : symbol -> symbol -> bool
val full_name : symbol -> string
val param_mode_name : param_mode -> string
