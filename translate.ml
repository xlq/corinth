(* Read the parse tree and create symbols. *)

open Symtab

type translation_state = {
    ts_root: symbol;
    ts_scope: symbol;
}

let new_translation_state root = {
    ts_root = root;
    ts_scope = root;
}

let rec trans_unit ts (loc, name, decls) =
    match name with
        | [name1] ->
            trans_decls {ts with ts_scope = create_sym ts.ts_scope loc name1 Unit} decls
        | name1::name ->
            trans_unit {ts with ts_scope = find_or_create_sym ts.ts_scope loc name1}
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
    | Parse_tree.Sub_decl(loc, name, params, return_type) ->
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
        sub_sym.sym_type <- match return_type with
            | Some rt -> Some (trans_type {ts with ts_scope = sub_sym} rt)
            | None -> None

and trans_type ts = function
    | Parse_tree.Integer ->
        Integer_type
