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
    mutable sym_parameters: symbol list;
    mutable sym_param_mode: param_mode;
    mutable sym_base_class: symbol option;
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
        sym_base_class = None;
    } in sym

let describe_symbol sym =
    match sym.sym_kind with
        | Unit       -> "unit"
        | Variable   -> "variable"
        | Subprogram ->
            begin match sym.sym_type with
                | Some _ -> "function"
                | None -> "procedure"
            end
        | Parameter  -> "parameter"
        | Class_type -> "class"

let undefined loc name =
    Errors.semantic_error loc ("Identifier `" ^ name ^ "' is undefined.");
    raise Errors.Compile_error

let find_or_create_sym parent loc name kind =
    try List.find (fun s -> s.sym_name = name) parent.sym_locals
    with Not_found ->
        let new_sym = {
            sym_parent = parent;
            sym_kind = kind;
            sym_name = name;
            sym_first_seen = loc;
            sym_defined = None;
            sym_type = None;
            sym_locals = [];
            sym_parameters = [];
            sym_param_mode = Const_param;
            sym_base_class = None;
        } in parent.sym_locals <- new_sym :: parent.sym_locals; new_sym

let create_sym parent loc name kind =
    let sym = find_or_create_sym parent loc name kind in
    match sym with
        | {sym_defined = Some loc'} ->
            Errors.semantic_error loc ("Symbol `" ^ name ^ "' already defined.");
            Errors.semantic_error loc' ("`" ^ name ^ "' was previously defined here.");
            raise Errors.Compile_error
        | {sym_defined = None} ->
            sym.sym_defined <- Some loc; sym

let check_sym_kind loc kinds expected sym =
    if List.exists ((=) sym.sym_kind) kinds then sym
    else begin
        (* Wrong symbol kind. *)
        Errors.semantic_error loc
            ((String.capitalize expected)
             ^ " expected but " ^ describe_symbol sym
             ^ " `" ^ sym.sym_name ^ "' found.");
        raise Errors.Compile_error
    end

let search_locals sym loc name kinds expected =
    match begin try Some (List.find (fun s -> s.sym_name = name) sym.sym_locals)
    with Not_found -> None end with
        | Some sym -> Some (check_sym_kind loc kinds expected sym)
        | None -> None

let search_scope scope loc name kinds expected =
    let rec search scope =
        match search_locals scope loc name kinds expected with
            | None ->
                if scope == scope.sym_parent then None
                else search scope.sym_parent
            | Some sym -> Some sym
    in match search scope with
        | Some sym -> sym
        | None ->
            undefined loc name

let search_for_dotted_name scope loc dname kinds expected =
    match dname with
        | [] -> assert false
        | [name] -> search_scope scope loc name kinds expected
        | first::parts ->
            let rec traverse sym = function
                | [] -> assert false
                | [name] ->
                    begin match search_locals sym loc name kinds expected with
                        | Some sym -> sym
                        | None ->
                            undefined loc name
                    end
                | name::tail ->
                    begin match search_locals sym loc name [Unit] "unit" with
                        | Some sym -> traverse sym tail
                        | None ->
                            undefined loc name
                    end
            in traverse (search_scope scope loc first [Unit] "unit") parts
