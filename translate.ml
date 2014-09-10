(* Read the parse tree and create symbols. *)

open Symtab

type todo =
    | Todo_class_defn of Parse_tree.decl list * symbol
    | Todo_sub_defn of Parse_tree.stmt list * symbol

type translation_state = {
    ts_root: symbol;
    ts_scope: symbol;
    ts_todo: todo list ref;
    ts_block: istmt list ref option;
}

let new_translation_state root = {
    ts_root = root;
    ts_scope = root;
    ts_todo = ref [];
    ts_block = None;
}

let todo ts x =
    ts.ts_todo := x :: !(ts.ts_todo)

let emit ts x =
    match ts.ts_block with
        | None -> assert false
        | Some code -> code := (!code) @ [x] (* XXX: horribly inefficient *)

let rec trans_unit ts (loc, name, decls) =
    match name with
        | [name1] ->
            trans_decls {ts with ts_scope = create_sym ts.ts_scope loc name1 Unit} decls
        | name1::name ->
            trans_unit {ts with ts_scope = find_or_create_sym ts.ts_scope loc name1 Unit}
                (loc, name, decls)
        | [] -> assert false

and trans_decls ts = List.iter (trans_decl ts)

and trans_decl ts = function
    | Parse_tree.Var_decl(loc, names, ttype) ->
        let ttype' = trans_type ts ttype in
        List.iter (fun name ->
            let new_sym = create_sym ts.ts_scope loc name Variable in
            new_sym.sym_type <- Some ttype'
        ) names
    | Parse_tree.Sub_decl(loc, name, params, return_type, body) -> begin
        let sub_sym = create_sym ts.ts_scope loc name Subprogram in
        List.iter (fun (loc, mode, names, ttype) ->
            let ttype' = trans_type {ts with ts_scope = sub_sym} ttype in
            List.iter (fun name ->
                let param_sym = create_sym sub_sym loc name Parameter in
                param_sym.sym_type <- Some ttype';
                param_sym.sym_param_mode <- match mode with
                    | Parse_tree.Const_param -> Const_param
                    | Parse_tree.Var_param -> Var_param
                    | Parse_tree.Out_param -> Out_param
            ) names
        ) params;
        sub_sym.sym_type <- (match return_type with
            | Some rt -> Some (trans_type {ts with ts_scope = sub_sym} rt)
            | None -> None);
        todo ts (Todo_sub_defn(body, sub_sym))
    end
    | Parse_tree.Type_decl(loc, name, Parse_tree.Class_defn(loc2, base_class, decls)) ->
        let base_class' = match base_class with
            | Some base_class ->
                Some (search_for_dotted_name ts.ts_scope loc2 base_class [Class_type] "base class")
            | None -> None in
        let type_sym = create_sym ts.ts_scope loc name Class_type in
        type_sym.sym_base_class <- base_class';
        todo ts (Todo_class_defn(decls, type_sym))

and trans_type ts = function
    | Parse_tree.Integer ->
        Integer_type
    | Parse_tree.Named_type(loc, name) ->
        Named_type(search_for_dotted_name ts.ts_scope loc name [Class_type] "type")

and trans_stmts ts = List.iter (trans_stmt ts)

and trans_stmt ts = function
    | Parse_tree.Assignment(loc, lhs, rhs) ->
        let rhs' = trans_expr ts rhs in
        let lhs' = trans_lvalue ts lhs in
        (* XXX: Type-checking! *)
        emit ts (Assignment(loc, lhs', rhs'))

and trans_expr ts = function
    | Parse_tree.Name(loc, name) ->
        let symbol = search_for_dotted_name ts.ts_scope loc name
            [Variable; Subprogram; Parameter; Class_type]
            "expression" in
        (* XXX: More stuff! *)
        Name(loc, symbol)
    | Parse_tree.Binop(loc, lhs, op, rhs) ->
        let lhs' = trans_expr ts lhs in
        let rhs' = trans_expr ts rhs in
        (* XXX: Type-checking! *)
        Binop(loc, lhs',
            (match op with
                | Parse_tree.Add -> Add
                | Parse_tree.Subtract -> Subtract
                | Parse_tree.Multiply -> Multiply
                | Parse_tree.Divide -> Divide)
            , rhs')

and trans_lvalue ts e =
    let e' = trans_expr ts e in
    (* XXX *)
    e'

let finish_trans ts =
    List.iter (function
        | Todo_class_defn(decls, class_sym) ->
            trans_decls {ts with ts_scope = class_sym} decls
        | Todo_sub_defn(body, sub_sym) ->
            let block = ref [] in
            trans_stmts {ts with
                ts_scope = sub_sym;
                ts_block = Some block} body;
            sub_sym.sym_code <- Some !block;

            (* XXX: Don't do this here! *)
            let c_state = Codegen_c.new_state () in
            Codegen_c.trans_sub c_state sub_sym
    ) !(ts.ts_todo)
