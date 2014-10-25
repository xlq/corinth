open Misc

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
    mutable sym_defined: loc option;
    mutable sym_type: ttype option;
    mutable sym_locals: symbol list;
    mutable sym_param_mode: param_mode;
    mutable sym_base_class: symbol option;
    mutable sym_code: istmt list option;
    mutable sym_selected: bool;
    mutable sym_translated: bool;
    mutable sym_backend_translated: bool;
}

and param_mode = Const_param | Var_param | Out_param

and ttype =
    | Integer_type  (* This is temporary, for development *)
    | Named_type of symbol

and istmt =
    | Assignment of loc * iexpr * iexpr

and iexpr =
    | Name of loc * symbol
    | Binop of loc * iexpr * binop * iexpr
    | Field_access of loc * iexpr * symbol

and binop = Add | Subtract | Multiply | Divide

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
        sym_defined = None;
        sym_type = None;
        sym_locals = [];
        sym_param_mode = Const_param;
        sym_base_class = None;
        sym_code = None;
        sym_selected = false;
        sym_translated = false;
        sym_backend_translated = false;
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
        print_endline ("Creating sym " ^ name ^ " under " ^ parent.sym_name);
        let new_sym = {
            sym_parent = parent;
            sym_kind = kind;
            sym_name = name;
            sym_defined = None;
            sym_type = None;
            sym_locals = [];
            sym_param_mode = Const_param;
            sym_base_class = None;
            sym_code = None;
            sym_selected = false;
            sym_translated = false;
            sym_backend_translated = false;
        } in parent.sym_locals <- parent.sym_locals @ [new_sym]; new_sym

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

let find_local sym loc name kinds expected =
    if not sym.sym_translated then begin
        Errors.internal_error loc ("`" ^ sym.sym_name ^ "' is not translated yet.")
    end else match search_locals sym loc name kinds expected with
        | Some sym -> sym
        | None ->
            undefined loc name

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

let parameters sym =
    List.find_all (fun s -> s.sym_kind = Parameter) sym.sym_locals

let find_needed_syms sym =
    let result = ref [] in
    let needed x =
        x.sym_selected <- true;
        result := x :: !result in
    let rec search sym =
        if sym.sym_selected then () else
        match sym.sym_kind with
            | Unit -> assert false
            | Variable -> needed sym; search_type (unsome sym.sym_type)
            | Parameter -> search_type (unsome sym.sym_type)
            | Class_type -> needed sym; List.iter search sym.sym_locals
            | Subprogram ->
                needed sym;
                (match sym.sym_type with None -> () | Some t -> search_type t);
                List.iter search (parameters sym)
    and search_type = function
        | Integer_type -> ()
        | Named_type(sym) -> search sym
    and search_istmt = function
        | Assignment(_, lhs, rhs) ->
            search_iexpr lhs; search_iexpr rhs
    and search_iexpr = function
        | Name(_, sym) -> search sym
        | Binop(_, lhs, _, rhs) -> search_iexpr lhs; search_iexpr rhs
        | Field_access(_, lhs, _) -> search_iexpr lhs
    in
    search sym;
    List.iter search_istmt (unsome sym.sym_code);
    List.iter (fun sym -> sym.sym_selected <- false) !result;
    !result
