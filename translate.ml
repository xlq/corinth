(* Read the parse tree and create symbols. *)

open Symtab
open Errors

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
    (* Variable definition *)
    | Parse_tree.Var_decl(loc, names, ttype) ->
        let ttype' = trans_type ts ttype in
        List.iter (fun name ->
            let new_sym = create_sym ts.ts_scope loc name Variable in
            new_sym.sym_type <- Some ttype'
        ) names
    (* Subprogram definition *)
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
    (* Class declaration *)
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
        let head::tail = name in
        let sym = ref (search_scope ts.ts_scope loc head [Unit; Variable; Parameter] "expression") in
        let expr = ref None in

        List.iter (fun name ->
            match !sym with
                | {sym_kind = Unit} ->
                    sym := find_local !sym loc name [Variable; Parameter; Subprogram] "expression"
                | {sym_kind = Variable | Parameter;
                   sym_type = Some(Named_type({sym_kind=Class_type} as cls))}
                -> begin
                    let field = find_local cls loc name [Variable; Subprogram] "field, method or property" in
                    match field.sym_kind with
                        | Variable ->
                            expr := Some(Field_access(loc,
                                (match !expr with
                                    | None -> Name(loc, !sym) 
                                    | Some e -> e), field));
                            sym := field
                end
        ) tail;
        begin match !sym.sym_kind with
            | Variable | Parameter -> ()
            | Unit | Subprogram | Class_type ->
                Errors.semantic_error loc
                    ("Expression expected but "
                        ^ describe_symbol !sym ^ " `"
                        ^ !sym.sym_name ^ "' found.");
                raise Errors.Compile_error
        end;
        begin match !expr with
            | None -> Name(loc, !sym)
            | Some e -> e
        end

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

and check_lvalue ts = function
    | Name(loc, sym) -> begin
        match sym.sym_kind, sym.sym_param_mode with
            | Parameter, Const_param ->
                semantic_error loc
                    ("Cannot assign to immutable parameter `" ^
                     sym.sym_name ^ "'.");
                raise Compile_error
            | Parameter, (Var_param | Out_param) -> ()
      end
    | Binop(loc, _, _, _) ->
        semantic_error loc
            ("Cannot assign to the result of a binary operation.");
        raise Compile_error
    | Field_access(loc, lhs, field) ->
        (* XXX: Check field access level, etc. *)
        check_lvalue ts lhs (* lhs must also be l-value *)

and trans_lvalue ts e =
    let e' = trans_expr ts e in
    check_lvalue ts e'; e'

let finish_trans ts =
    let subs = ref [] in
    List.iter (function
        | Todo_class_defn(decls, class_sym) ->
            (* Class definition *)
            trans_decls {ts with ts_scope = class_sym} decls;
            class_sym.sym_translated <- true
        | Todo_sub_defn _ -> ()
    ) !(ts.ts_todo);
    List.iter (function
        | Todo_class_defn _ -> ()
        | Todo_sub_defn(body, sub_sym) ->
            let block = ref [] in
            trans_stmts {ts with
                ts_scope = sub_sym;
                ts_block = Some block} body;
            sub_sym.sym_code <- Some !block;
            subs := sub_sym :: !subs;
            sub_sym.sym_translated <- true
    ) !(ts.ts_todo);

    (* XXX: Don't do this here! *)
    let c_state = Codegen_c.new_state () in
    List.iter (Codegen_c.trans_sub c_state) !subs
