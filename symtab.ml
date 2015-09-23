open Big_int
open Misc

type loc = Lexing.position
type dotted_name = string list

type binop = Add | Subtract | Multiply | Divide | LT | GT | LE | GE | EQ | NE | And | Or

type sym_kind =
    | Unit
    | Var
    | Proc
    | Class
    | Class_proc
    | Type_sym
    | Type_param
    | Param
    | Const
    | Proc_type_sym

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
    mutable sym_implementations: symbol list;
    mutable sym_param_mode: param_mode;
    mutable sym_code: istmt list option;
    mutable sym_imported: string option;
    mutable sym_const: iexpr option;
    mutable sym_selected: bool;
    mutable sym_translated: bool; (* Body has been translated?
        If false, some children may be missing. *)
    mutable sym_backend_translated: int;
}

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
    mutable tvar_link: ttype option;
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

and classarg =
    | Implement of symbol * (symbol * symbol) list
    | Forward of int

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
    | Dispatch of int * symbol * tbinds
    | Apply of loc * iexpr * (proc_param * iexpr) list (* parameter bindings *)
    | Record_cons of loc * ttype (* record type *) * (string * iexpr) list
    | Field_access of loc * iexpr * string
    | Binop of loc * iexpr * binop * iexpr
    | Deref of loc * iexpr
    | Not of loc * iexpr
    | New of loc * ttype * iexpr
    | Bind of ttype * iexpr

let dummy_loc = {
    Lexing.pos_fname = "<built-in>";
    Lexing.pos_lnum = 0;
    Lexing.pos_bol = 0;
    Lexing.pos_cnum = 0;
}

let tvar_counter = ref 0
let new_tvar origin =
    tvar_counter := !tvar_counter + 1;
    { tvar_origin = origin;
      tvar_id = !tvar_counter;
      tvar_link = None }

let is_kind kind sym = sym.sym_kind = kind

let new_root_sym () =
    let rec sym = {
        sym_parent = sym;
        sym_kind = Unit;
        sym_name = "";
        sym_defined = Some dummy_loc;
        sym_type = None;
        sym_locals = [];
        sym_virtual = false;
        sym_implementations = [];
        sym_param_mode = Const_param;
        sym_code = None;
        sym_imported = None;
        sym_abstract = false;
        sym_const = None;
        sym_selected = false;
        sym_translated = false;
        sym_backend_translated = 0;
    } in sym

let describe_sym sym =
    match sym.sym_kind with
        | Unit       -> "unit"
        | Var        -> "variable"
        | Proc       -> "procedure"
        | Class      -> "class"
        | Class_proc -> "class procedure"
        | Type_sym   -> "type"
        | Type_param -> "type parameter"
        | Param      -> "parameter"

let create_sym parent loc name kind =
    let new_sym = {
        sym_parent = parent;
        sym_kind = kind;
        sym_name = name;
        sym_defined = Some loc;
        sym_type = None;
        sym_locals = [];
        sym_virtual = false;
        sym_implementations = [];
        sym_param_mode = Const_param;
        sym_code = None;
        sym_imported = None;
        sym_abstract = false;
        sym_const = None;
        sym_selected = false;
        sym_translated = false;
        sym_backend_translated = 0;
    } in
    parent.sym_locals <- parent.sym_locals @ [new_sym];
    new_sym

let get_type_params sym = List.filter (is_kind Type_param) sym.sym_locals
let get_params sym = List.filter (is_kind Param) sym.sym_locals

let string_of_tvar v = "t" ^ string_of_int v.tvar_id

let rec string_of_type = function
    | TNone -> "(no type)"
    | TBoolean -> "bool"
    | TInteger -> "int"
    | TChar -> "char"
    | TName s -> s.sym_name
    | TVar {tvar_link=Some t} -> string_of_type t
    | TVar v -> string_of_tvar v
    | TPointer ty -> "^" ^ string_of_type ty
    | TRecord record ->
        "{" ^ String.concat ", " (List.map (fun field ->
            field.field_name ^ ": " ^ string_of_type field.field_type) record.rec_fields) ^ "}"
    | TProc proc ->
        "proc (" ^ String.concat ", " (List.map (fun param ->
            (match param.param_mode with
                | Const_param -> ""
                | Var_param -> "var "
                | Out_param -> "out "
                ) ^ (match param.param_name with Some s -> s ^ ": " | None -> "")
                  ^ string_of_type param.param_type
            ) proc.proc_params) ^ ")"
            ^ (match proc.proc_return with
                | TNone -> ""
                | ty -> ": " ^ string_of_type ty)
    | TEnum elements ->
        "(" ^ String.concat ", " (List.map (fun s -> s.sym_name) elements) ^ ")"
    | TUniv(v, ty) ->
        "{" ^ string_of_tvar v
            (* ^ (match v.tvar_origin with
                | Some {sym_kind=Type_param; sym_name=s} -> " from " ^ s
                | Some {sym_kind=Var; sym_name=s} -> " from " ^ s ^ "'Type"
                | None -> "") *) ^ "} " ^ string_of_type ty

let rec sym_is_grandchild parent sym =
    if parent == sym then true
    else if sym.sym_parent == sym then false
    else sym_is_grandchild parent sym.sym_parent

let full_name sym =
    String.concat "."
        (let rec follow r s =
            if s.sym_parent == s then r
            else follow (s.sym_name::r) s.sym_parent
         in follow [] sym)

let param_mode_name = function
    | Const_param -> "an input parameter"
    | Var_param -> "a `var' parameter"
    | Out_param -> "a `out' parameter"
