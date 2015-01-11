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
    | Temp

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
    | Named_type of symbol * (symbol * ttype) list
    | Pointer_type of ttype
    | Record_type of symbol option
    | Proc_type of symbol

and istmt =
    | Call of loc * iexpr * (symbol * iexpr) list
    | Assign of loc * iexpr * iexpr
    | Return of loc * iexpr option

and iexpr =
    | Name of loc * symbol
    | Int_literal of loc * big_int
    | Apply of loc * iexpr * (symbol * iexpr) list
    | Record_cons of loc * symbol (* record type *) * (symbol * iexpr) list
    | Field_access of loc * iexpr * symbol
    | Binop of loc * iexpr * binop * iexpr

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
        sym_param_mode = Const_param;
        sym_code = None;
        sym_selected = false;
        sym_translated = false;
        sym_backend_translated = false;
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
        sym_param_mode = Const_param;
        sym_code = None;
        sym_selected = false;
        sym_translated = false;
        sym_backend_translated = false;
    } in
    parent.sym_locals <- parent.sym_locals @ [new_sym];
    new_sym

let temp_counter = ref 0

let create_temp parent loc ttype =
    incr temp_counter;
    let new_sym = {
        sym_parent = parent;
        sym_kind = Temp;
        sym_name = string_of_int !temp_counter;
        sym_defined = Some loc;
        sym_type = Some ttype;
        sym_locals = [];
        sym_dispatching = false;
        sym_param_mode = Const_param;
        sym_code = None;
        sym_selected = false;
        sym_translated = false;
        sym_backend_translated = false;
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

let rec string_of_type = function
    | Integer_type -> "int"
    | Named_type(sym, []) -> sym.sym_name
    | Named_type(sym, args) ->
        sym.sym_name ^ "<" ^ String.concat ", "
            (List.map (fun (param, arg) ->
                param.sym_name ^ " => " ^ string_of_type arg) args) ^ ">"
    | Pointer_type t -> "^" ^ string_of_type t

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
