open Big_int
open Misc

type loc = Lexing.position
type dotted_name = string list

type binop = Add | Subtract | Multiply | Divide | LT | GT | LE | GE | EQ | NE

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
    mutable sym_tconstraints: (symbol * tbinds) list; (* type parameter constraints *)
    mutable sym_implementations: symbol list;
    mutable sym_param_mode: param_mode;
    mutable sym_code: istmt list option;
    mutable sym_imported: bool;
    mutable sym_abstract: bool;
    mutable sym_const: iexpr option;
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
    | Dispatch of int * symbol * tbinds
    | Apply of loc * iexpr * (symbol * iexpr) list (* parameter bindings *)
                           * tbinds (* type parameter bindings *)
                           * (symbol * (symbol * symbol) list) list ref (* classes *)
    | Record_cons of loc * symbol (* record type *) * (symbol * iexpr) list
    | Field_access of loc * iexpr * symbol
    | Binop of loc * iexpr * binop * iexpr
    | Deref of loc * iexpr

let dummy_loc = {
    Lexing.pos_fname = "<built-in>";
    Lexing.pos_lnum = 0;
    Lexing.pos_bol = 0;
    Lexing.pos_cnum = 0;
}

let is_kind kind sym = sym.sym_kind = kind

let new_root_sym () =
    let rec sym = {
        sym_parent = sym;
        sym_kind = Unit;
        sym_name = "";
        sym_defined = Some dummy_loc;
        sym_type = None;
        sym_locals = [];
        sym_tconstraints = [];
        sym_implementations = [];
        sym_param_mode = Const_param;
        sym_code = None;
        sym_imported = false;
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
        sym_tconstraints = [];
        sym_implementations = [];
        sym_param_mode = Const_param;
        sym_code = None;
        sym_imported = false;
        sym_abstract = false;
        sym_const = None;
        sym_selected = false;
        sym_translated = false;
        sym_backend_translated = 0;
    } in
    parent.sym_locals <- parent.sym_locals @ [new_sym];
    new_sym

let get_type_params sym =
    List.filter (is_kind Type_param) sym.sym_locals

let rec get_fields sym =
    match sym with
        | {sym_kind=Type_sym; sym_type=Some(Record_type(base)); sym_locals=fields} ->
            fields @ (match base with Some t -> get_fields t | None -> [])
        | _ -> raise (Failure "get_fields")

let get_params sym =
    List.filter (is_kind Param) sym.sym_locals

let rec string_of_type_int substs = function
    | No_type -> "<no type>"
    | Boolean_type -> "bool"
    | Integer_type -> "int"
    | Char_type -> "char"
    | Named_type({sym_kind=Type_param} as tp, []) ->
        begin match maybe_assq tp substs with
            | None -> tp.sym_name
            | Some t -> string_of_type_int substs t
        end
    | Named_type(sym, []) -> sym.sym_name
    | Named_type(sym, args) ->
        sym.sym_name ^ "<" ^ String.concat ", "
            (List.map (fun (param, arg) ->
                param.sym_name ^ "=" ^ string_of_type_int substs arg) args) ^ ">"
    | Pointer_type t -> "^" ^ string_of_type_int substs t
    | Proc_type _ -> "<proc type>"

let string_of_type t = string_of_type_int [] t

let string_of_type_2 substs t =
    let short = string_of_type_int [] t in
    let long = string_of_type_int substs t in
    if short = long then short
    else short ^ " (" ^ long ^ ")"

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

let rec iter_type_params_in f = function
    | No_type | Boolean_type | Integer_type | Char_type -> ()
    | Named_type({sym_kind=Type_param} as tp, []) -> f tp
    | Named_type(_, args) -> List.iter (fun (_, t) -> iter_type_params_in f t) args
    | Pointer_type t -> iter_type_params_in f t
    | Record_type _ | Proc_type _ -> ()
