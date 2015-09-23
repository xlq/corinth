(* First pass after parsing.
   This pass mainly populates the symbol table, resolves symbol references
   and performs type checking. *)

open Symtab
open Types
open Errors
open Misc

type ('a, 'b) alternative = Left of 'a | Right of 'b

let present = function
    | Some _ -> true
    | None -> false

type todo =
    | Todo_type
    | Todo_class
    | Todo_proc
    | Todo_abstract_proc
    | Todo_apply_check
    (* XXX: Dependency graph? *)

type translation_state = {
    ts_root: symbol;
    ts_scope: symbol;
    ts_todo: (todo * (unit -> unit)) list ref;
    ts_block: istmt list ref option;
    ts_tctx: Types.context;
}

let coerce ts situation t1 t2 =
    prerr_endline ("coerce " ^ string_of_type t1 ^ " to " ^ string_of_type t2);
    Types.coerce ts.ts_tctx situation t1 t2 (* short-hand *)

let actual_type = function
    | TName {sym_kind=Type_sym; sym_type=Some t} -> t
    | t -> t

let new_translation_state root = {
    ts_root = root;
    ts_scope = root;
    ts_todo = ref [];
    ts_block = None;
    ts_tctx = Types.new_context ();
}

let todo ts todo_kind f =
    ts.ts_todo := (todo_kind, f) :: !(ts.ts_todo)

let emit ts x =
    match ts.ts_block with
        | None -> assert false
        | Some code -> code := (!code) @ [x] (* XXX: horribly inefficient *)

(* Return the name of the given symbol suitable for an error message. *)
let name_for_error ts sym =
    if (sym_is_grandchild ts.ts_scope sym) || (ts.ts_scope == sym) then sym.sym_name
    else full_name sym

let wrong_sym_kind ts loc bad_sym expected =
    Errors.semantic_error loc
        (String.capitalize expected ^ " expected but "
            ^ describe_sym bad_sym ^ " `" ^ name_for_error ts bad_sym ^ "' found.");
    raise Errors.Compile_error

let check_for_duplicate_definition scope loc name =
    List.iter (fun sym ->
        if sym.sym_name = name then begin
            Errors.semantic_error loc
                ("Redefinition of symbol `" ^ name ^ "'.");
            Errors.semantic_error (unsome sym.sym_defined)
                (String.capitalize (describe_sym sym)
                 ^ " `" ^ name ^ "' was first defined here.");
            raise Errors.Compile_error
        end
    ) scope.sym_locals

(* Search current scope and parent scopes/etc. for the name. *)
let search_scopes ts loc name =
    let rec this scope results =
        (* Search locals *)
        let results = match maybe_find (fun s -> s.sym_name = name) scope.sym_locals with
            | Some sym -> (sym,[])::results
            | None -> results in
        (* Search classes in scope *)
        (*
        let results = if scope.sym_kind = Proc then
            List.fold_left (fun results (tclass, targs) ->
                List.fold_left (fun results cls_proc ->
                    if cls_proc.sym_kind = Class_proc && cls_proc.sym_name = name then
                        (* This class proc is a candidate.
                           Must include type parameter bindings! *)
                        (cls_proc, targs)::results
                    else results
                ) results tclass.sym_locals
            ) results scope.sym_tconstraints
        else results in
        *)
        parent scope results
    and parent scope results =
        if scope.sym_parent == scope then results
        else this scope.sym_parent results
    in match this ts.ts_scope [] with
        | [] -> None
        | [(sym,tbinds)] -> Some (sym, tbinds)
        | (sym,_)::lots ->
            (* TODO: eliminate type-mismatched candidates (i.e. implement overloading) *)
            Errors.semantic_error loc ("`" ^ name ^ "' is ambiguous.");
            Errors.semantic_error (unsome sym.sym_defined) "It could refer to this.";
            List.iter (fun (sym, _) ->
                Errors.semantic_error (unsome sym.sym_defined) "Or this.") lots;
            raise Errors.Compile_error

let undefined_symbol ts loc name =
    Errors.semantic_error loc ("`" ^ name ^ "' is undefined.");
    raise Errors.Compile_error

let search_scopes_or_fail ts loc name =
    match search_scopes ts loc name with
        | Some sym -> sym
        | None -> undefined_symbol ts loc name

let find_dotted_name ts loc name =
    let head::tail = name in
    let start, tbinds = search_scopes_or_fail ts loc head in
    let rec follow sym tbinds name =
        match sym.sym_kind, tbinds, name with
            | _, _, [] -> (sym, tbinds)
            | (Unit|Class), [], next_bit::tail ->
                match maybe_find (fun child -> child.sym_name = next_bit) sym.sym_locals with
                    | Some child -> (child, [])
                    | None ->
                        Errors.semantic_error loc (String.capitalize (describe_sym sym) ^ " `"
                            ^ name_for_error ts sym ^ "' has no symbol named `" ^ next_bit ^ "'.");
                        raise Compile_error
    in follow start tbinds tail

let expect_type ts loc target_type situation source_type =
    try coerce ts situation source_type target_type
    with Type_mismatch err ->
        (*Errors.semantic_error loc
            ("Type mismatch " ^ why_target ^ ": expected `"
                ^ string_of_type target_type
                ^ "' but got `" ^ string_of_type source_type ^ "'.")*)
        Errors.type_error loc err

(* p_name is a function to get the name of a parameter *)
let match_args_to_params loc what p_name params pos_args named_args =
    let remaining_params = ref (enumerate params) in
    let matched_params = ref [] in
    List.iter (fun pos_arg ->
        match !remaining_params with
            | (i,param)::params ->
                remaining_params := params;
                matched_params := (i, param, pos_arg) :: !matched_params
            | [] ->
                Errors.semantic_error loc ("Too many " ^ what ^ ".");
                raise Errors.Compile_error
    ) pos_args;
    List.iter (fun (name, arg) ->
        let rec search = function
            | (i,param)::params when name = p_name param ->
                matched_params := (i, param, arg) :: !matched_params;
                params
            | (i,param)::params ->
                (i,param) :: search params
            | [] ->
                match maybe_find (fun (i, param, arg) ->
                    name = p_name param)
                !matched_params with
                    | Some (i, param, arg) ->
                        Errors.semantic_error loc
                            ("Parameter `" ^ name ^ "' given twice.");
                        raise Errors.Compile_error
                    | None ->
                        Errors.semantic_error loc
                            ("No such parameter `" ^ name ^ "'.");
                        raise Errors.Compile_error
        in remaining_params := search !remaining_params
    ) named_args;
    List.iter (fun (i, remaining_param) ->
        Errors.semantic_error loc
            ("Missing parameter `" ^ p_name remaining_param ^ "'.")
    ) !remaining_params;
    List.map (fun (_,param,arg) -> (param, arg))
        (List.sort (fun (i1,_,_) (i2,_,_) -> compare i1 i2) !matched_params)

let rec loc_of_expr = function
    | Parse_tree.Name(loc, _)
    | Parse_tree.Int_literal(loc, _)
    | Parse_tree.String_literal(loc, _)
    | Parse_tree.Char_literal(loc, _)
    | Parse_tree.Apply(loc, _, _) -> loc

let rec loc_of_iexpr = function
    | Name(loc, _)
    | Bool_literal(loc, _)
    | Int_literal(loc, _)
    | String_literal(loc, _)
    | Char_literal(loc, _)
    | Apply(loc, _, _)
    | Record_cons(loc, _, _)
    | Field_access(loc, _, _)
    | Binop(loc, _, _, _)
    | Deref(loc, _)
    | New(loc, _, _)
        -> loc

let construct_type_of_proc proc_sym =
    List.fold_right (fun {sym_kind=Type_param; sym_type=Some (TVar v)} proc_type ->
        TUniv(v, proc_type)
    ) (get_type_params proc_sym) (TProc {
        proc_loc = unsome proc_sym.sym_defined;
        proc_params = List.map (fun param ->
            { param_loc = unsome param.sym_defined;
              param_name = Some param.sym_name;
              param_mode = param.sym_param_mode;
              param_type = unsome param.sym_type }
            ) (get_params proc_sym);
        proc_return = unsome proc_sym.sym_type })

let rec trans_unit ts = function
    | Parse_tree.Unit(loc, [name], decls) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let new_unit = create_sym ts.ts_scope loc name Unit in
        trans_decls {ts with ts_scope = new_unit} decls;
        new_unit
    | Parse_tree.Unit(loc, name1::name, decls) ->
        trans_unit {ts with ts_scope =
            match maybe_find (fun s -> s.sym_name = name1) ts.ts_scope.sym_locals with
                | Some existing_unit -> existing_unit
                | None ->
                    (* Parent unit is not yet translated or defined. *)
                    let new_unit = create_sym ts.ts_scope loc name1 Unit in
                    new_unit.sym_defined <- None; (* not actually defined here *)
                    new_unit
            } (Parse_tree.Unit(loc, name, decls))
    | Parse_tree.Unit(_, [], _) -> assert false

and trans_decls ts = List.iter (trans_decl ts)

and trans_params ts proc_sym params return_type =
    let ts = {ts with ts_scope = proc_sym} in
    List.iter (fun (loc, name, ttype, mode) ->
        let ttype' = match ttype with
            | None -> None
            | Some t -> Some (trans_type ts t) in
        check_for_duplicate_definition proc_sym loc name;
        let param_sym = create_sym proc_sym loc name Param in
        param_sym.sym_type <- ttype';
        param_sym.sym_param_mode <- mode
    ) params;
    proc_sym.sym_type <- Some (match return_type with
        | None -> TNone
        | Some ty -> trans_type ts ty)

and trans_decl ts = function
    (*
    (* Variable definition *)
    | Parse_tree.Var_decl(loc, names, ttype) ->
        let ttype' = trans_type ts ttype in
        List.iter (fun name ->
            let new_sym = create_sym ts.ts_scope loc name Variable in
            new_sym.sym_type <- Some ttype'
        ) names
    *)

    (* Procedure definition *)
    | Parse_tree.Proc_decl(loc, is_virtual, name, type_params, params, return_type, maybe_implements, body) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let proc_sym = create_sym ts.ts_scope loc name Proc in
        proc_sym.sym_virtual <- is_virtual;
        ignore (trans_type_params {ts with ts_scope = proc_sym} type_params);
        trans_params ts proc_sym params return_type;
        todo ts Todo_proc (fun () ->
            (*begin match maybe_implements with
                | None -> ()
                | Some name ->
                    match find_dotted_name ts loc name with
                        | ({sym_kind=Class_proc} as cls_proc), [] ->
                            assert (cls_proc.sym_parent.sym_kind = Class);
                            ignore (exi_quant_param ts cls_proc.sym_parent (fun ts ->
                                check_func_is_instance ts loc cls_proc proc_sym
                            ));
                            cls_proc.sym_implementations <- proc_sym :: cls_proc.sym_implementations
                        | bad_sym, _ -> wrong_sym_kind ts loc bad_sym "class proc" (* TODO: better loc *)
            end;*) (* TODO TODO TODO *)

            match body with
                | Parse_tree.Abstract -> ()
                | Parse_tree.Body code ->
                    let stmts = ref [] in
                    trans_stmts {ts with ts_scope = proc_sym;
                                         ts_block = Some stmts} code;
                    proc_sym.sym_code <- Some !stmts;
                    proc_sym.sym_translated <- true
        )

    | Parse_tree.Proc_import(loc, name, type_params, params, return_type, maybe_implements, c_name) ->
        (* TODO: There is much in common with Proc_decl: merge! *)
        check_for_duplicate_definition ts.ts_scope loc name;
        let proc_sym = create_sym ts.ts_scope loc name Proc in
        ignore (trans_type_params {ts with ts_scope = proc_sym} type_params);
        trans_params ts proc_sym params return_type;
        proc_sym.sym_imported <- Some c_name;
        todo ts Todo_proc (fun () ->
            (*begin match maybe_implements with
                | None -> ()
                | Some name ->
                    match find_dotted_name ts loc name with
                        | ({sym_kind=Class_proc} as cls_proc), [] ->
                            assert (cls_proc.sym_parent.sym_kind = Class);
                            ignore (exi_quant_param ts cls_proc.sym_parent (fun ts ->
                                check_func_is_instance ts loc cls_proc proc_sym
                            ));
                            cls_proc.sym_implementations <- proc_sym :: cls_proc.sym_implementations
                        | bad_sym, _ -> wrong_sym_kind ts loc bad_sym "class proc" (* TODO: better loc *)
            end*) (* TODO TODO TODO *) ()
        )

    | Parse_tree.Type_decl(loc, name, type_params, Parse_tree.Type_alias(other)) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let other = trans_type ts other in
        let type_sym = create_sym ts.ts_scope loc name Type_sym in
        type_sym.sym_type <- Some other
    (* Record type declaration *)
    | Parse_tree.Type_decl(loc, name, type_params, Parse_tree.Record_type(fields)) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let type_sym = create_sym ts.ts_scope loc name Type_sym in
        let type_params = trans_type_params {ts with ts_scope = type_sym} type_params in
        (* TODO: base record *)
        todo ts Todo_type (fun () ->
            let ts = {ts with ts_scope = type_sym} in
            let fields = List.rev (List.fold_left (fun fields (loc, name, ty) ->
                let ty = trans_type ts ty in
                match name with
                    | Some name ->
                        if (List.exists (fun f -> f.field_name = name) fields) then begin
                            Errors.semantic_error loc ("Duplicate field `" ^ name ^ "'.")
                        end;
                        { field_loc = loc;
                          field_name = name;
                          field_type = ty } :: fields
            ) [] fields) in
            type_sym.sym_type <- Some
                (List.fold_right (fun {sym_kind=Type_param; sym_type=Some (TVar v)} rec_type ->
                    TUniv(v, rec_type)) type_params (TRecord { rec_loc = loc;
                                                               rec_fields = fields }))
        )
    | Parse_tree.Var_decl(loc, name, maybe_type, maybe_init) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let var_sym = create_sym ts.ts_scope loc name Var in
        begin match maybe_type with
            | Some specified_type ->
                (* Type is specified. *)
                let specified_type = trans_type ts specified_type in
                var_sym.sym_type <- Some specified_type;
                begin match maybe_init with
                    | Some init ->
                        (* Initial value must be of correct type. *)
                        let init, init_type, _ = trans_expr ts (Some specified_type) init in
                        expect_type ts loc specified_type
                            [SVar_init var_sym]
                            init_type;
                        emit ts (Assign(loc, Name(loc, var_sym), init))
                    | None -> ()
                end
            | None ->
                (* No type is specified. Type is inferred. *)
                begin match maybe_init with
                    | Some init ->
                        let init, init_type, _ = trans_expr ts None init in
                        var_sym.sym_type <- Some init_type;
                        emit ts (Assign(loc, Name(loc, var_sym), init))
                    | None ->
                        Errors.semantic_error loc
                            ("Variable must be initialised or have its type specified.")
                end
        end
    | Parse_tree.Const_decl(loc, name, expr) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let const_sym = create_sym ts.ts_scope loc name Const in
        let expr, expr_type, _ = trans_expr ts None expr in
        const_sym.sym_type <- Some expr_type;
        const_sym.sym_const <- Some expr

and trans_type_params ts =
    List.map (fun (loc, name) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let tp = create_sym ts.ts_scope loc name Type_param in
        let v = new_tvar (Some tp) in
        tp.sym_type <- Some (TVar v);
        tp
    )

and trans_type ts = function
    | Parse_tree.Integer_type -> TInteger
    | Parse_tree.Boolean_type -> TBoolean
    | Parse_tree.Char_type -> TChar
    | Parse_tree.Named_type(loc, [name]) ->
        begin match search_scopes_or_fail ts loc name with
            | {sym_kind=Type_sym} as typ, [] ->
                TName typ
            | {sym_kind=Type_param} as typ_p, [] ->
                begin match typ_p.sym_type with
                    | Some (TVar v) -> TVar v
                    | _ -> assert false
                end
            | bad_sym, _ -> wrong_sym_kind ts loc bad_sym "type"
        end
    (*
    | Parse_tree.Applied_type(loc, ttype, (pos_args, named_args)) ->
        begin match trans_type ts ttype with
            | 

            | Named_type(type_sym, []) ->
                begin match get_type_params type_sym with
                    | [] ->
                        Errors.semantic_error loc
                            ("Type `" ^ name_for_error ts type_sym ^ "' has no parameters.");
                        raise Errors.Compile_error
                    | type_params ->
                        let matched_args = match_args_to_params loc "type arguments"
                            type_params pos_args named_args in
                        Named_type(type_sym,
                            List.map (fun (param, arg) ->
                                (param, trans_type ts arg)) matched_args)
                end
            | Named_type(type_sym, _) as ttype ->
                Errors.semantic_error loc
                    ("Type " ^ string_of_type ttype ^ " already has arguments.");
                raise Errors.Compile_error
            | ttype ->
                Errors.semantic_error loc
                    ("Type " ^ string_of_type ttype ^ " cannot take arguments.");
                raise Errors.Compile_error
        end
    *)
    | Parse_tree.Pointer_type(ttype) ->
        TPointer(trans_type ts ttype)
    (*
    | Parse_tree.Proc_type(loc, constr_type_params, params, return_type) ->
        let ptypesym = create_sym ts.ts_scope loc "" Proc_type_sym in
        trans_type_params {ts with ts_scope = ptypesym} constr_type_params;
        trans_params ts ptypesym params return_type;
        Proc_type(ptypesym, [])
    *)
    | Parse_tree.Enum_type(elements) ->
        let elements = List.map (fun (loc, name) ->
            check_for_duplicate_definition ts.ts_scope loc name;
            create_sym ts.ts_scope loc name Const
            ) elements in
        let ty = TEnum(elements) in
        List.iter (fun el -> el.sym_type <- Some ty) elements;
        ty

and trans_stmts ts = List.iter (trans_stmt ts)

and trans_stmt ts = function
    | Parse_tree.Decl decl -> trans_decl ts decl
    | Parse_tree.Expr((Parse_tree.Apply _) as e) ->
        let call, tcall, _ = trans_expr ts None e in
        expect_type ts (loc_of_iexpr call) TNone [SCall_none] tcall;
        begin match call with
            | Apply(loc, proc, args) ->
                emit ts (Call(loc, proc, args))
            | _ -> assert false
        end
    | Parse_tree.Expr(e) ->
        Errors.semantic_error
            (loc_of_expr e)
            "Statement expected but expression found."
    | Parse_tree.Assign(loc, dest, src) ->
        let dest, dest_type, lvalue = trans_expr ts None dest in
        if not lvalue then begin
            Errors.semantic_error loc ("Cannot assign to this expression.");
            raise Compile_error
        end;
        let src, src_type, _ = trans_expr ts (Some dest_type) src in
        expect_type ts loc dest_type [SAssign] src_type;
        emit ts (Assign(loc, dest, src))
    | Parse_tree.Return(loc, Some e) ->
        begin match ts.ts_scope with
            | {sym_kind=Proc; sym_type=Some TNone} ->
                Errors.semantic_error (loc_of_expr e)
                    ("Procedure `" ^ name_for_error ts ts.ts_scope
                     ^ "' has no return type, so cannot return a value.")
            | {sym_kind=Proc; sym_type=Some t} ->
                let e, e_type, _ = trans_expr ts (Some t) e in
                expect_type ts (loc_of_iexpr e) t [SReturn_stat]  e_type;
                emit ts (Return(loc, Some e))
            | _ -> assert false
        end
    | Parse_tree.Return(loc, None) ->
        begin match ts.ts_scope with
            | {sym_kind=Proc; sym_type=Some TNone} ->
                emit ts (Return(loc, None))
            | {sym_kind=Proc; sym_type=Some _} ->
                Errors.semantic_error loc
                    ("Procedure `" ^ name_for_error ts ts.ts_scope
                     ^ "' must return a value.")
            | _ -> assert false
        end
    | Parse_tree.If_stmt(parts, else_part) ->
        emit ts (If_stmt(
            List.map (fun (loc, condition, body) ->
                let condition, condition_type, _ = trans_expr ts
                    (Some TBoolean) condition in
                expect_type ts loc TBoolean [SCondition] condition_type;
                let body' = ref [] in
                trans_stmts {ts with ts_block = Some body'} body;
                (loc, condition, !body')
            ) parts,
            match else_part with
                | None -> None
                | Some (loc, else_body) ->
                    let body' = ref [] in
                    trans_stmts {ts with ts_block = Some body'} else_body;
                    Some (loc, !body')
        ))
    | Parse_tree.While_stmt(loc, cond, body) ->
        let cond, cond_type, _ = trans_expr ts (Some TBoolean) cond in
        expect_type ts loc TBoolean [SCondition] cond_type;
        let body' = ref [] in
        trans_stmts {ts with ts_block = Some body'} body;
        emit ts (While_stmt(loc, cond, !body'))

(* Translate expression and return (iexpr * ttype * bool) tuple.
   target_type is the type of the expression's context, if known.
   This is necessary when the type of the expression cannot be determined
   from the expression alone (e.g. var x: record_type := {1, 2}).
   The type of the result of trans_expr IS NOT checked against target_type!
   The types may be incompatible - the caller must check/coerce.
   Third value is true iff expression is an l-value. *)

and trans_expr ts (target_type: ttype option) = function
    | Parse_tree.Name(loc, ["false"]) ->
        (Bool_literal(loc, false), TBoolean, false)
    | Parse_tree.Name(loc, ["true"]) ->
        (Bool_literal(loc, true), TBoolean, false)
    | Parse_tree.Name(loc, name) ->
        let name_start :: name_tail = name in
        let loc_of_result = function
            | Left s -> (unsome s.sym_defined)
            | Right(_, _, _, defloc) -> defloc
        in
        let result_of_sym loc sym =
            match sym with
                | {sym_kind=Unit} -> Left(sym)
                | {sym_kind=Var}
                | {sym_kind=Param; sym_param_mode=Var_param|Out_param} ->
                    Right(Name(loc, sym), unsome sym.sym_type, true, unsome sym.sym_defined)
                | {sym_kind=Const}
                | {sym_kind=Param; sym_param_mode=Const_param} ->
                    Right(Name(loc, sym), unsome sym.sym_type, false, unsome sym.sym_defined)
                | {sym_kind=Proc} ->
                    Right(Name(loc, sym), construct_type_of_proc sym, false, unsome sym.sym_defined)
        in

        (* Search for first part of name. *)
        let rec find_name_start scope results =
            (* Search locals. *)
            let results = match maybe_find (fun s -> s.sym_name = name_start) scope.sym_locals with
                | Some sym -> (result_of_sym loc sym)::results
                | None -> results in
            (*
            (* Search classes in scope. *)
            let results = if scope.sym_kind = Proc then
                List.fold_left (fun results (class_index, (tclass, targs)) ->
                    List.fold_left (fun results cls_proc ->
                        if cls_proc.sym_kind = Class_proc && cls_proc.sym_name = name_start then
                            (* This class proc is a candidate. *)
                            (Right(Dispatch(class_index, cls_proc, targs),
                                   Proc_type(cls_proc, targs), false, unsome cls_proc.sym_defined))::results
                        else results
                    ) results tclass.sym_locals
                ) results (enumerate scope.sym_tconstraints)
            else results in
            *)
            (* Search parent scope. *)
            if scope.sym_parent == scope then results
            else find_name_start scope.sym_parent results
        in
        begin match find_name_start ts.ts_scope [] with
            | [] -> undefined_symbol ts loc name_start
            | (result1::result2::resultN) -> 
                Errors.semantic_error loc ("`" ^ name_start ^ "' is ambiguous.");
                Errors.semantic_error (loc_of_result result1) "It could refer to this.";
                List.iter (fun result ->
                    Errors.semantic_error (loc_of_result result) "Or this.") (result2::resultN);
                raise Errors.Compile_error
            | [result] ->
                (* Follow the rest of the name. *)
                let rec follow_name_tail result name_tail =
                    match result, name_tail with
                        | Left(unit_sym), name::name_tail ->
                            begin match maybe_find (fun s -> s.sym_name == name) (unit_sym.sym_locals) with
                                | None -> Errors.semantic_error loc
                                    ("Unit `" ^ name_for_error ts unit_sym ^ "' has no symbol named `"
                                        ^ name ^ "'."); raise Errors.Compile_error
                                | Some sym -> follow_name_tail (result_of_sym loc sym) name_tail
                            end
                        | Right(expr, ty, lvalue, _), name::name_tail ->
                            (* Look field up in record type. *)
                            begin match ty with
                                | TRecord record ->
                                    begin match maybe_find (fun field -> field.field_name = name) record.rec_fields with
                                        | Some field ->
                                            follow_name_tail (Right(Field_access(loc, expr, field.field_name),
                                                              field.field_type,
                                                              lvalue,
                                                              field.field_loc
                                                            )) name_tail
                                        | None ->
                                            Errors.semantic_error loc
                                                ((* "Type `" ^ name_for_error ts type_sym ^ ' has*) "No field named `"
                                                    ^ name ^ "'.");
                                            (* TODO: Aquire type name! *)
                                            raise Errors.Compile_error
                                    end
                                | wrong_type ->
                                    Errors.semantic_error loc
                                        ("Type `" ^ string_of_type ty ^ "' has no fields.");
                                    raise Errors.Compile_error
                            end
                        | Left(unit_sym), [] ->
                            Errors.semantic_error loc ("Expression expected but unit `"
                                ^ name_for_error ts unit_sym ^ "' found.");
                            raise Errors.Compile_error
                        | Right(expr, ty, lvalue, _), [] ->
                            (expr, ty, lvalue)
                in follow_name_tail result name_tail
        end
    | Parse_tree.Field_access(loc, e, name) ->
        (* TODO: Merge with above. *)
        let e, ty, lv = trans_expr ts None e in
        begin match ty with
            | TRecord record ->
                begin match maybe_find (fun field -> field.field_name = name) record.rec_fields with
                    | Some field -> (Field_access(loc, e, field.field_name), field.field_type, lv)
                    | None ->
                        Errors.semantic_error loc
                            ((* "Type `" ^ name_for_error ts type_sym ^ ' has*) "No field named `"
                                ^ name ^ "'.");
                        (* TODO: Aquire type name! *)
                        raise Errors.Compile_error
                end
            | wrong_type ->
                Errors.semantic_error loc
                    ("Type `" ^ string_of_type ty ^ "' has no fields.");
                raise Errors.Compile_error
        end
    | Parse_tree.Int_literal(loc, n) ->
        (Int_literal(loc, n), TInteger, false)
    | Parse_tree.String_literal(loc, s) ->
        (String_literal(loc, s), TPointer TChar, false)
    | Parse_tree.Char_literal(loc, s) ->
        (Char_literal(loc, s), TChar, false)
    | Parse_tree.Apply(loc, proc, (pos_args, named_args)) ->
        (* Translate callee. *)
        let proc, proc_type, _ = trans_expr ts None proc in
        (* Translate arguments. *)
        let pos_args' = List.map (fun e -> let e, ty, lv = trans_expr ts None e in None, e, ty, lv) pos_args in
        let named_args' = List.map (fun (name, e) -> let e, ty, lv = trans_expr ts None e in Some name, e, ty, lv) named_args in
        (* Construct proc type from arguments given. *)
        let args_proc_type = {
            proc_loc = loc;
            proc_params =
                List.map (fun (name, e, ty, lv) ->
                    { param_loc = loc_of_iexpr e;
                      param_mode = if lv then Var_param else Const_param;
                      param_name = name;
                      param_type = ty }) (pos_args' @ named_args');
            proc_return = match target_type with
                | Some ty -> ty
                | None -> TVar (new_tvar None) } in
        (*coerce ts proc_type (TProc args_proc_type);*)
        expect_type ts loc (TProc args_proc_type)
            [SApply(match proc with | Name(_,s) -> Some s | _ -> None)] proc_type;
        (Apply(loc, proc,
            List.map2 (fun param (_, e, _, _) -> (param, e))
                      args_proc_type.proc_params
                      (pos_args' @ named_args')),
         args_proc_type.proc_return, false)
    | Parse_tree.Record_cons(loc, (pos_fields, named_fields)) ->
        (* Get record type from context. *)
        let rec_info = match target_type with
            | Some (TName {sym_kind=type_sym; sym_type=Some (TRecord rec_info)}) -> rec_info
            | Some (TRecord rec_info) -> rec_info
            | Some t ->
                Errors.semantic_error loc
                    ("Value of type `" ^ string_of_type t
                        ^ "' expected but record constructor found.");
                    raise Errors.Compile_error
            | None -> Errors.semantic_error loc
                ("Record type cannot be determined by context.");
                raise Errors.Compile_error
        in
        let rec_type = unsome target_type in
        (Record_cons(loc, rec_type,
            List.map (fun (field, expr) ->
                let expr, expr_type, _ = trans_expr ts (Some field.field_type) expr in
                expect_type ts loc field.field_type [SRecord_cons]  expr_type;
                (field.field_name, expr)
            ) (match_args_to_params loc "record fields" (fun f -> f.field_name)
                rec_info.rec_fields pos_fields named_fields)
         ), rec_type, false)
    | Parse_tree.Binop(loc, lhs, (And|Or as op), rhs) ->
        let lhs, lhs_type, _ = trans_expr ts (Some TBoolean) lhs in
        let rhs, rhs_type, _ = trans_expr ts (Some TBoolean) rhs in
        expect_type ts (loc_of_iexpr lhs) TBoolean [SBoolean_op] lhs_type;
        expect_type ts (loc_of_iexpr rhs) TBoolean [SBoolean_op] rhs_type;
        (Binop(loc, lhs, op, rhs), TBoolean, false)
    | Parse_tree.Binop(loc, lhs, op, rhs) ->
        let lhs, lhs_type, _ = trans_expr ts None lhs in
        let rhs, rhs_type, _ = trans_expr ts None rhs in
        (* match_types ts loc lhs_type rhs_type; *)
        expect_type ts loc rhs_type [SBinop] lhs_type; (* TODO: properly *)
        (Binop(loc, lhs, op, rhs),
            (match op with
                | Add|Subtract|Multiply|Divide -> lhs_type
                | LT|GT|LE|GE|EQ|NE -> TBoolean), false)
    | Parse_tree.Deref(loc, ptr) ->
        let ptr, ptr_type, _ = trans_expr ts None ptr in
        begin match actual_type ptr_type with
            | TPointer t ->
                (Deref(loc, ptr), t, true)
            | _ ->
                Errors.semantic_error loc
                    ("Cannot dereference value of type `"
                        ^ string_of_type ptr_type ^ "'.");
                raise Compile_error
        end
    | Parse_tree.Not(loc, e) ->
        let e, ty, _ = trans_expr ts None e in
        expect_type ts (loc_of_iexpr e) TBoolean [SBoolean_op] ty;
        (Not(loc, e), TBoolean, false)
    | Parse_tree.New(loc, e) ->
        let e, ty, lv = trans_expr ts
            (match target_type with
                | None -> None
                | Some(TPointer ty) -> Some ty
                | Some ty ->
                    Errors.semantic_error loc
                        ("Value of type " ^ string_of_type ty
                            ^ "' expected but `new' found.");
                    raise Errors.Compile_error
            ) e in
        (New(loc, ty, e), TPointer ty, false)

let finish_trans ts unit =
    while !(ts.ts_todo) <> [] do
        let items = !(ts.ts_todo) in
        ts.ts_todo := [];

        List.iter (fun todo_kind ->
            List.iter (fun (kind', f) ->
                if todo_kind = kind' then f () else ()
            ) items
        ) [Todo_type; Todo_class; Todo_proc; Todo_abstract_proc; Todo_apply_check]
    done;
        
    (* XXX: Don't do this here! *)
    let c_state = Codegen_lua.new_state ts.ts_root in
    List.iter (Codegen_lua.translate c_state)
        (List.filter (is_kind Proc) unit.sym_locals)
