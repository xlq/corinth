open Big_int
open Misc

type loc = Lexing.position
type dotted_name = string list

type binop = Add | Subtract | Multiply | Divide | LT | GT | LE | GE | EQ | NE

type sym_kind =
    | Unit
    | Var
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
    mutable sym_dispatching: bool; (* Proc's ttype parameter is dispatching (declared "disp") *)
    mutable sym_dispatched_to: symbol list;
    mutable sym_base_proc: symbol option; (* Base proc for overriding proc. *)
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
    | Char_literal of loc * string
    | Apply of loc * iexpr * (symbol * iexpr) list
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

let new_root_sym () =
    let rec sym = {
        sym_parent = sym;
        sym_kind = Unit;
        sym_name = "";
        sym_defined = Some dummy_loc;
        sym_type = None;
        sym_locals = [];
        sym_dispatching = false;
        sym_dispatched_to = [];
        sym_base_proc = None;
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
        sym_dispatching = false;
        sym_dispatched_to = [];
        sym_base_proc = None;
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
    List.filter (fun sym -> sym.sym_kind = Type_param) sym.sym_locals

let rec get_fields sym =
    match sym with
        | {sym_kind=Type_sym; sym_type=Some(Record_type(base)); sym_locals=fields} ->
            fields @ (match base with Some t -> get_fields t | None -> [])
        | _ -> raise (Failure "get_fields")

let get_params sym =
    List.filter (fun s -> s.sym_kind = Param) sym.sym_locals

let rec string_of_type_int expand_tp = function
    | No_type -> "<no type>"
    | Boolean_type -> "bool"
    | Integer_type -> "int"
    | Char_type -> "char"
    | Named_type({sym_kind=Type_param; sym_type=Some t}, []) when expand_tp -> string_of_type_int true t
    | Named_type(sym, []) -> sym.sym_name
    | Named_type(sym, args) ->
        sym.sym_name ^ "<" ^ String.concat ", "
            (List.map (fun (param, arg) ->
                param.sym_name ^ "=" ^ string_of_type_int expand_tp arg) args) ^ ">"
    | Pointer_type t -> "^" ^ string_of_type_int expand_tp t
    | Proc_type _ -> "<proc type>"

let string_of_type t =
    let short = string_of_type_int false t in
    let long = string_of_type_int true t in
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

let is_dispatching sym =
    assert (sym.sym_kind = Proc);
    List.exists (function
        | {sym_kind=Type_param; sym_dispatching=true} -> true
        | _ -> false) sym.sym_locals

(* Return list of dispatching procedures a type parameter must be dispatchable to. *)
let get_dispatch_list tp =
    let rec collect visited all = function
        | [] -> all
        | tp::rest when List.exists ((==) tp) visited -> collect visited all rest
        | tp::rest ->
            assert (tp.sym_kind == Type_param);
            collect (tp::visited) (tp.sym_parent::all) (List.rev_append tp.sym_dispatched_to rest)
    in collect [] [] tp.sym_dispatched_to
