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

let dummy_loc = {
    Lexing.pos_fname = "<built-in>";
    Lexing.pos_lnum = 0;
    Lexing.pos_bol = 0;
    Lexing.pos_cnum = 0;
}

let new_root_symbol () =
    let rec sym = {
        sym_parent = sym;
        sym_kind = Unit;
        sym_name = "";
        sym_first_seen = dummy_loc;
        sym_defined = None;
        sym_type = None;
        sym_locals = [];
        sym_parameters = [];
        sym_param_mode = Const_param;
    } in sym

let find_or_create_sym parent loc name =
    try List.find (fun s -> s.sym_name = name) parent.sym_locals
    with Not_found ->
        let new_sym = {
            sym_parent = parent;
            sym_kind = Undefined;
            sym_name = name;
            sym_first_seen = loc;
            sym_defined = None;
            sym_type = None;
            sym_locals = [];
            sym_parameters = [];
            sym_param_mode = Const_param;
        } in parent.sym_locals <- new_sym :: parent.sym_locals; new_sym

let create_sym parent loc name kind =
    let sym = find_or_create_sym parent loc name in
    match sym with
        | {sym_defined = Some loc'} ->
            Errors.semantic_error loc ("Symbol `" ^ name ^ "' already defined.");
            Errors.semantic_error loc' ("`" ^ name ^ "' was previously defined here.");
            raise Errors.Compile_error
        | {sym_defined = None} ->
            sym.sym_kind <- kind;
            sym.sym_defined <- Some loc;
            sym
