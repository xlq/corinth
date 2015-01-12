(* First pass after parsing.
   This pass mainly populates the symbol table, resolves symbol references
   and performs type checking. *)

open Symtab
open Errors
open Misc

type ('a, 'b) alternative = Left of 'a | Right of 'b

let present = function
    | Some _ -> true
    | None -> false

type todo =
    | Todo_type of Parse_tree.decl * symbol
    | Todo_proc of Parse_tree.stmt list * symbol

type translation_state = {
    ts_root: symbol;
    ts_scope: symbol;
    ts_todo: todo list ref;
    ts_block: istmt list ref option;
    ts_exists: symbol list; (* list of symbols whose type parameters
                               are existentially quantified and can be unified *)
}

let new_translation_state root = {
    ts_root = root;
    ts_scope = root;
    ts_todo = ref [];
    ts_block = None;
    ts_exists = [];
}

(* Mark type parameters of the given symbol as existentially quantified
   while f is called with the translation state. *)
let exi_quant_param ts sym f =
    assert (List.for_all (function
        | {sym_kind=Type_param; sym_type=None} -> true
        | {sym_kind=Type_param; sym_type=Some _} -> false
        | _ -> true) sym.sym_locals);
    let result = f {ts with ts_exists = sym :: ts.ts_exists} in
    List.iter (function
        | {sym_kind=Type_param; sym_type=Some t} as sym -> sym.sym_type <- None
        | _ -> ()) sym.sym_locals;
    result

let todo ts x =
    ts.ts_todo := x :: !(ts.ts_todo)

let emit ts x =
    match ts.ts_block with
        | None -> assert false
        | Some code -> code := (!code) @ [x] (* XXX: horribly inefficient *)

(* Return the name of the given symbol suitable for an error message. *)
let name_for_error ts sym =
    if (sym_is_grandchild ts.ts_scope sym) || (ts.ts_scope == sym) then sym.sym_name
    else full_name sym

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
let rec search_scopes ts name =
    match maybe_find (fun s -> s.sym_name = name) ts.ts_scope.sym_locals with
        | Some sym -> Some sym
        | None when ts.ts_scope.sym_parent == ts.ts_scope -> None
        | None -> search_scopes {ts with ts_scope = ts.ts_scope.sym_parent} name

let undefined_symbol ts loc name =
    Errors.semantic_error loc ("`" ^ name ^ "' is undefined.");
    raise Errors.Compile_error

let search_scopes_or_fail ts loc name =
    match search_scopes ts name with
        | Some sym -> sym
        | None -> undefined_symbol ts loc name

let rec unwind_unifs stop_at = function
    | unifs when unifs == stop_at -> ()
    | [] -> ()
    | sym::tail -> sym.sym_type <- None; unwind_unifs stop_at tail

let reset_unifs sym =
    List.iter (function
        | {sym_kind=Type_param; sym_type=Some t} as param ->
            prerr_endline ("Resetting " ^ full_name param ^ " -> " ^ string_of_type t);
            param.sym_type <- None
        | _ -> ()
    ) sym.sym_locals

let unify ts loc v t =
    (* TODO: Occurs check? *)
    assert (match v.sym_type with None -> true | Some _ -> false);
    if not (List.exists ((==) v.sym_parent) ts.ts_exists) then begin
        Errors.semantic_error loc
            ("Cannot use type parameter `" ^ v.sym_name
                ^ "' as type `" ^ string_of_type t
                ^ "' because `" ^ v.sym_name
                ^ "' could be anything!"); (* I don't know what sensible message to put here. *)
        raise Compile_error
    end;
    (*ts.ts_unifications := v :: !(ts.ts_unifications);*)
    v.sym_type <- Some t;
    prerr_endline ("Unifying " ^ full_name v ^ " -> " ^ string_of_type t)

(* Substitute type parameters for type arguments. *)
let rec subst_tparams tparams = function
    | No_type -> No_type
    | Boolean_type -> Boolean_type
    | Integer_type -> Integer_type
    | Char_type -> Char_type
    | Named_type({sym_kind=Type_param} as param, []) ->
        snd (List.find (fun (param', arg') -> param == param') tparams)
    | Pointer_type t -> Pointer_type (subst_tparams tparams t)

(* Apply current type parameter substitutions. *)
let rec follow_tparams = function
    | No_type -> No_type
    | Boolean_type -> Boolean_type
    | Integer_type -> Integer_type
    | Char_type -> Char_type
    | Named_type({sym_kind=Type_param; sym_type=Some t}, []) -> t
    | Pointer_type t -> Pointer_type (follow_tparams t)

(* Return the actual type (follow Named_type) *)
let rec actual_type = function
    | (Integer_type | Pointer_type _ | Record_type _) as t -> t
    | Named_type({sym_kind=Type_sym; sym_type=Some t}, _) -> t

let rec same_type t1 t2 =
    match t1, t2 with
        | No_type, No_type -> true
        | Pointer_type(t1), Pointer_type(t2) -> same_type t1 t2
        
        | Named_type(s1, []), Named_type(s2, []) -> s1 == s2
        | Named_type({sym_kind=Type_sym; sym_type=Some t1}, []), t2
        | t1, Named_type({sym_kind=Type_sym; sym_type=Some t2}, []) -> same_type t1 t2

        | No_type, _ | _, No_type
        | Integer_type, _ | _, Integer_type
        | Pointer_type _, _ | _, Pointer_type _ -> false

exception Type_mismatch

let rec coerce_int ts loc target_type why_target source_type =
    match target_type, source_type with
        | t1, t2 when t1 == t2 -> () (* short-cut if the types are exactly the same *)
        | No_type, No_type -> ()
        | Pointer_type(t1), Pointer_type(t2) -> coerce_int ts loc t1 why_target t2
        | Named_type(s1, []), Named_type(s2, []) when s1 == s2 -> () (* same symbol *)
        | Named_type({sym_kind=Type_param; sym_type=Some t1}, []), t2
        | t2, Named_type({sym_kind=Type_param; sym_type=Some t1}, []) ->
            (* Follow type parameter unification. *)
            coerce_int ts loc t1 why_target t2
        | Named_type({sym_kind=Type_param; sym_type=None} as tp, []), t2 ->
            (* Target type parameter isn't unified, so it could be anything.
               Now we know it must be t2. *)
            unify ts loc tp t2
        | Named_type(s1, params1), Named_type(s2, params2) when s1 == s2 ->
            List.iter2 (fun (param1, arg1) (param2, arg2) ->
                assert (param1 == param2);
                coerce_int ts loc arg1
                    ("for parameter `" ^ param1.sym_name ^ "' of type `"
                        ^ name_for_error ts s1 ^ "'") arg2
            ) params1 params2
        (* Type aliases. *)
        | Named_type({sym_kind=Type_sym; sym_type=Some t1}, []), t2
        | t1, Named_type({sym_kind=Type_sym; sym_type=Some t2}, []) ->
            coerce_int ts loc t1 why_target t2
        (* Type mismatches. *)
        | No_type, _ | _, No_type
        | Integer_type, _ | _, Integer_type
        | Boolean_type, _ | _, Boolean_type
        | Char_type, _ | _, Char_type
        | Pointer_type _, _ | _, Pointer_type _
        | Named_type _, Named_type _ ->
            raise Type_mismatch

let coerce ts loc target_type why_target source_type =
    try coerce_int ts loc target_type why_target source_type
    with Type_mismatch ->
        Errors.semantic_error loc
            ("Type mismatch " ^ why_target ^ ": expected `"
                ^ string_of_type target_type
                ^ "' but got `" ^ string_of_type source_type ^ "'.")

let rec match_types_int ts loc t1 t2 =
    match t1, t2 with
        | t1, t2 when t1 == t2 -> ()
        | No_type, No_type -> ()
        | Integer_type, Integer_type -> ()
        | Pointer_type(t1), Pointer_type(t2) -> match_types_int ts loc t1 t2
        | Named_type(s1, []), Named_type(s2, []) when s1 == s2 -> ()
        | Named_type({sym_kind=Type_param; sym_type=Some t1}, []), t2
        | t1, Named_type({sym_kind=Type_param; sym_type=Some t2}, []) ->
            match_types_int ts loc t1 t2
        | Named_type({sym_kind=Type_param; sym_type=None} as tp, []), t2 ->
            unify ts loc tp t2
        | t1, Named_type({sym_kind=Type_param; sym_type=None} as tp, []) ->
            unify ts loc tp t1
        (* Type aliases. *)
        | Named_type({sym_kind=Type_sym; sym_type=Some t1}, []), t2
        | t1, Named_type({sym_kind=Type_sym; sym_type=Some t2}, []) ->
            match_types_int ts loc t1 t2
        (* Type mismatches *)
        | No_type, _ | _, No_type
        | Integer_type, _ | _, Integer_type
        | Pointer_type _, _ | _, Pointer_type _
        | Named_type _, Named_type _ ->
            raise Type_mismatch

let match_types ts loc t1 t2 =
    try match_types_int ts loc t1 t2
    with Type_mismatch ->
        Errors.semantic_error loc
            ("Incompatible types: `"
                ^ string_of_type t1 ^ "' and `"
                ^ string_of_type t2 ^ "'.")

let match_args_to_params loc what params pos_args named_args =
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
            | (i,param)::params when name = param.sym_name ->
                matched_params := (i, param, arg) :: !matched_params;
                params
            | (i,param)::params ->
                (i,param) :: search params
            | [] ->
                match maybe_find (fun (i, param, arg) ->
                    name = param.sym_name)
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
            ("Missing parameter `" ^ remaining_param.sym_name ^ "'.")
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
    | Name(loc, _) -> loc
    | Int_literal(loc, _)
    | String_literal(loc, _)
    | Char_literal(loc, _)
    | Apply(loc, _, _)
    | Record_cons(loc, _, _)
    | Field_access(loc, _, _)
    | Binop(loc, _, _, _)
    | Deref(loc, _)
        -> loc

let rec trans_unit ts = function
    | Parse_tree.Unit(loc, [name], decls) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let new_unit = create_sym ts.ts_scope loc name Unit in
        trans_decls {ts with ts_scope = new_unit} decls
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
    | (Parse_tree.Proc_decl(loc, name, type_params, params, return_type, _) as decl)
    | (Parse_tree.Proc_import(loc, name, type_params, params, return_type) as decl) -> begin
        check_for_duplicate_definition ts.ts_scope loc name;
        let proc_sym = create_sym ts.ts_scope loc name Proc in
        (* Type parameters *)
        let type_params = trans_type_params {ts with ts_scope = proc_sym} type_params in
        let dispatching_type_param = List.fold_left (fun disp_tp tp ->
            if not tp.sym_dispatching then disp_tp else
            match disp_tp with
                | None -> Some tp
                | Some tp' ->
                    Errors.semantic_error (unsome tp'.sym_defined)
                        ("Only one type parameter can be marked as dispatching.");
                    Some tp'
        ) None type_params in
        (* Parameters *)
        List.iter (fun (loc, name, ttype, mode) ->
            let ttype' = match ttype with
                | None -> None
                | Some t -> Some (trans_type {ts with ts_scope = proc_sym} t) in
            check_for_duplicate_definition proc_sym loc name;
            let param_sym = create_sym proc_sym loc name Param in
            param_sym.sym_type <- ttype';
            param_sym.sym_param_mode <- mode
        ) params;
        (* Return type *)
        proc_sym.sym_type <- (match return_type with
            | Some rt -> Some (trans_type {ts with ts_scope = proc_sym} rt)
            | None -> Some No_type);
        match decl with
            | Parse_tree.Proc_decl(_, _, _, _, _, Some body) -> todo ts (Todo_proc(body, proc_sym))
            | Parse_tree.Proc_decl(_, _, _, _, _, None) -> proc_sym.sym_abstract <- true
            | Parse_tree.Proc_import(_, _, _, _, _) -> proc_sym.sym_imported <- true
    end
    | Parse_tree.Type_decl(loc, name, type_params, Parse_tree.Type_alias(other)) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let other = trans_type ts other in
        let type_sym = create_sym ts.ts_scope loc name Type_sym in
        type_sym.sym_type <- Some other
    (* Record type declaration *)
    | Parse_tree.Type_decl(loc, name, type_params, Parse_tree.Record_type(fields)) as decl ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let type_sym = create_sym ts.ts_scope loc name Type_sym in
        let type_params = trans_type_params {ts with ts_scope = type_sym} type_params in
        List.iter (fun tparam ->
            if tparam.sym_dispatching then
                Errors.semantic_error (unsome tparam.sym_defined)
                    ("`disp' only makes sense for procedures, not for types.")
        ) type_params;
        type_sym.sym_type <- Some (Record_type(None)); (* TODO: base record *)
        todo ts (Todo_type(decl, type_sym))
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
                        coerce ts loc specified_type
                            ("for initialisation of variable `" ^ name ^ "'")
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

and trans_type_params ts type_params =
    List.map (fun (loc, name, dispatching) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let new_param = create_sym ts.ts_scope loc name Type_param in
        new_param.sym_dispatching <- dispatching;
        new_param
    ) type_params

and trans_type ts = function
    | Parse_tree.Integer_type -> Integer_type
    | Parse_tree.Boolean_type -> Boolean_type
    | Parse_tree.Char_type -> Char_type
    | Parse_tree.Named_type(loc, [name]) ->
        begin match search_scopes_or_fail ts loc name with
            | {sym_kind=Type_sym} as typ ->
                Named_type(typ, [])
            | {sym_kind=Type_param} as typ_p ->
                Named_type(typ_p, [])
            | bad_sym ->
                Errors.semantic_error loc
                    ("Type expected but " ^ describe_sym bad_sym
                     ^ " `" ^ name_for_error ts bad_sym ^ "' found.");
                raise Errors.Compile_error
        end
    | Parse_tree.Applied_type(loc, ttype, (pos_args, named_args)) ->
        begin match trans_type ts ttype with
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
    | Parse_tree.Pointer_type(ttype) ->
        Pointer_type(trans_type ts ttype)

and trans_stmts ts = List.iter (trans_stmt ts)

and trans_stmt ts = function
    (*| Parse_tree.Assignment(loc, lhs, rhs) ->
        let rhs' = trans_expr ts rhs in
        let lhs' = trans_lvalue ts lhs in
        (* XXX: Type-checking! *)
        emit ts (Assignment(loc, lhs', rhs'))*)
    | Parse_tree.Decl decl -> trans_decl ts decl
    | Parse_tree.Expr((Parse_tree.Apply _) as e) ->
        let call, tcall, _ = trans_expr ts None e in
        begin match call, tcall with
            | Apply(loc, proc, args), No_type ->
                emit ts (Call(loc, proc, args))
            | Apply(loc, Name(_,({sym_kind=Proc} as proc_sym)), _), _ ->
                Errors.semantic_error loc
                    ("Proc `" ^ name_for_error ts proc_sym
                        ^ "' returns a value, so cannot be called as a statement.")
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
        coerce ts loc dest_type "for assignment" src_type;
        emit ts (Assign(loc, dest, src))
    | Parse_tree.Return(loc, Some e) ->
        begin match ts.ts_scope with
            | {sym_kind=Proc; sym_type=Some No_type} ->
                Errors.semantic_error (loc_of_expr e)
                    ("Procedure `" ^ name_for_error ts ts.ts_scope
                     ^ "' has no return type, so cannot return a value.")
            | {sym_kind=Proc; sym_type=Some t} ->
                let e, e_type, _ = trans_expr ts (Some t) e in
                coerce ts (loc_of_iexpr e) t ("for returned value") e_type;
                emit ts (Return(loc, Some e))
            | _ -> assert false
        end
    | Parse_tree.Return(loc, None) ->
        begin match ts.ts_scope with
            | {sym_kind=Proc; sym_type=Some No_type} ->
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
                    (Some Boolean_type) condition in
                coerce ts loc Boolean_type "for condition" condition_type;
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
        let cond, cond_type, _ = trans_expr ts (Some Boolean_type) cond in
        coerce ts loc Boolean_type "for condition" cond_type;
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
    | Parse_tree.Name(loc, name) ->
        let trans_sym sym =
            match sym with
                | {sym_kind=Unit} -> Left(sym)
                | {sym_kind=Var} | {sym_kind=Param; sym_param_mode=Var_param|Out_param} ->
                    Right(Name(loc, sym), unsome sym.sym_type, true)
                | {sym_kind=Param; sym_param_mode=Const_param} | {sym_kind=Const} ->
                    Right(Name(loc, sym), unsome sym.sym_type, false)
                | {sym_kind=Proc} ->
                    Right(Name(loc, sym), Proc_type (sym), false)
        in
        let rec trans_dotted_name = function
            | [base] -> trans_sym (search_scopes_or_fail ts loc base)
            | part::rest ->
                begin match trans_dotted_name rest with
                    | Left(unit_sym) ->
                        (* Look symbol up in unit. *)
                        begin match maybe_find (fun s -> s.sym_name = part) (unit_sym.sym_locals) with
                            | Some sym -> trans_sym sym
                            | None ->
                                Errors.semantic_error loc
                                    ("Unit `" ^ name_for_error ts unit_sym ^ "' has no symbol named `"
                                        ^ part ^ "'."); raise Errors.Compile_error
                        end
                    | Right(expr, tp, lvalue) ->
                        (* Look field up in record type. *)
                        begin match tp with
                            | Named_type({sym_kind=Type_sym; sym_type=Some(Record_type _)} as type_sym, tparams) ->
                                begin match maybe_find (fun s -> s.sym_name = part) (get_fields type_sym) with
                                    | Some field ->
                                        Right(Field_access(loc, expr, field), subst_tparams tparams (unsome field.sym_type), lvalue)
                                    | None ->
                                        Errors.semantic_error loc
                                            ("Type `" ^ name_for_error ts type_sym ^ "' has no field named `" ^ part ^ "'.");
                                        raise Errors.Compile_error
                                end
                            | wrong_type ->
                                Errors.semantic_error loc
                                    ("Type `" ^ string_of_type tp ^ "' has no fields.");
                                raise Errors.Compile_error
                        end
                end
        in begin match trans_dotted_name (List.rev name) with
            | Left(unit_sym) ->
                Errors.semantic_error loc
                    ("Expression expected but unit `" ^ name_for_error ts unit_sym ^ "' found.");
                raise Errors.Compile_error
            | Right(expr, tp, lvalue) -> (expr, tp, lvalue)
        end
    | Parse_tree.Int_literal(loc, n) ->
        (Int_literal(loc, n), Integer_type, false)
    | Parse_tree.String_literal(loc, s) ->
        (String_literal(loc, s), Pointer_type(Char_type), false)
    | Parse_tree.Char_literal(loc, s) ->
        (Char_literal(loc, s), Char_type, false)
    | Parse_tree.Apply(loc, proc, (pos_args, named_args)) ->
        let proc, proc_type, _ = trans_expr ts None proc in
        begin match proc_type with
            | Proc_type(proc_sym) ->
                (* proc_sym is either a Proc symbol or a Proc_type Type_sym symbol. *)
                exi_quant_param ts proc_sym (fun ts ->
                    let matched_args =
                        List.map (fun (param, arg) ->
                            assert (present param.sym_type);
                            let arg, arg_type, lvalue = trans_expr ts param.sym_type arg in
                            begin match param.sym_param_mode with
                                | Var_param | Out_param ->
                                    if not lvalue then begin
                                        Errors.semantic_error (loc_of_iexpr arg)
                                            ("Cannot assign to this expression (parameter `"
                                                ^ param.sym_name ^ "' is declared `"
                                                ^ (match param.sym_param_mode with Var_param -> "var"
                                                                                 | Out_param -> "out") ^ "'.");
                                    end
                                | Const_param -> ()
                            end;
                            coerce ts (loc_of_iexpr arg) (unsome param.sym_type)
                                ("for parameter `" ^ param.sym_name ^ "'") arg_type;
                            (param, arg)
                        ) (match_args_to_params loc "arguments"
                            (get_params proc_sym) pos_args named_args) in
                    (Apply(loc, proc, matched_args),
                     follow_tparams (unsome proc_sym.sym_type) (* return type *), false)
                )
        end
    | Parse_tree.Record_cons(loc, (pos_fields, named_fields)) ->
        (* Get record type from context. *)
        let rec_sym = match target_type with
            | Some(Named_type({sym_type=Some(Record_type _)} as sym, [])) -> sym
            | Some t -> Errors.semantic_error loc
                ("Value of type `" ^ string_of_type t
                    ^ "' expected but record constructor found.");
                raise Errors.Compile_error
            | None -> Errors.semantic_error loc
                ("Record type cannot be determined by context.");
                raise Errors.Compile_error
        in
        (* Match expressions to record's fields. *)
        (Record_cons(loc, rec_sym,
            List.map (fun (field, expr) ->
                assert (present field.sym_type);
                let expr, expr_type, _ = trans_expr ts field.sym_type expr in
                coerce ts loc (unsome field.sym_type)
                    ("for field `" ^ field.sym_name ^ "'") expr_type;
                (field, expr)
            ) (match_args_to_params loc "record fields"
                (get_fields rec_sym) pos_fields named_fields)
         ), Named_type(rec_sym, []), false)
    | Parse_tree.Binop(loc, lhs, op, rhs) ->
        let lhs, lhs_type, _ = trans_expr ts None lhs in
        let rhs, rhs_type, _ = trans_expr ts None rhs in
        match_types ts loc lhs_type rhs_type;
        (Binop(loc, lhs, op, rhs),
            (match op with
                | Add|Subtract|Multiply|Divide -> lhs_type
                | LT|GT|LE|GE|EQ|NE -> Boolean_type), false)
    | Parse_tree.Deref(loc, ptr) ->
        let ptr, ptr_type, _ = trans_expr ts None ptr in
        begin match actual_type ptr_type with
            | Pointer_type(t) ->
                (Deref(loc, ptr), t, true)
            | _ ->
                Errors.semantic_error loc
                    ("Cannot dereference value of type `"
                        ^ string_of_type ptr_type ^ "'.");
                raise Compile_error
        end


(*


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
*)

let finish_trans ts =
    let subs = ref [] in
    List.iter (function
        | Todo_type(Parse_tree.Type_decl(loc, name, type_params,
          Parse_tree.Record_type(fields)), type_sym) ->
            let ts = {ts with ts_scope = type_sym} in
            List.iter (fun (loc, name, ttype) ->
                let ttype' = trans_type ts ttype in
                match name with
                    | Some name ->
                        check_for_duplicate_definition type_sym loc name;
                        (create_sym type_sym loc name Var).sym_type <- Some ttype'
                    | None ->
                        (create_sym type_sym loc "" Var).sym_type <- Some ttype'
            ) fields
        | Todo_proc _ -> ()
    ) !(ts.ts_todo);
    List.iter (function
        | Todo_type _ -> ()
        | Todo_proc(stmts, proc_sym) ->
            let stmts' = ref [] in
            trans_stmts {ts with ts_scope = proc_sym;
                                 ts_block = Some stmts'} stmts;
            proc_sym.sym_code <- Some !stmts';
            subs := proc_sym :: !subs;
            proc_sym.sym_translated <- true
    ) !(ts.ts_todo);

    (* XXX: Don't do this here! *)
    let c_state = Codegen_c.new_state () in
    List.iter (Codegen_c.trans_sub c_state) !subs
