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
    | Todo_abstract_proc of symbol
    | Todo_apply_check of iexpr
    (* XXX: Dependency graph? *)

type translation_state = {
    ts_root: symbol;
    ts_scope: symbol;
    ts_todo: todo list ref;
    ts_block: istmt list ref option;
    ts_exi_quants: (symbol * (symbol -> ttype -> unit)) list;
}

let new_translation_state root = {
    ts_root = root;
    ts_scope = root;
    ts_todo = ref [];
    ts_block = None;
    ts_exi_quants = [];
}

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

let find_dotted_name ts loc name =
    let head::tail = name in
    List.fold_left (fun sym name ->
        if sym.sym_kind <> Unit then begin
            Errors.semantic_error loc "This doesn't make sense."; (* TODO: Proper error message, lol *)
            raise Compile_error
        end else match maybe_find (fun child -> child.sym_name = name) sym.sym_locals with
            | Some child -> child
            | None ->
                Errors.semantic_error loc
                    (String.capitalize (describe_sym sym)
                     ^ " `" ^ name_for_error ts sym ^ "' has nothing named `"
                     ^ name ^ "'.");
                raise Compile_error
    ) (search_scopes_or_fail ts loc head) tail

(* Call f with sym's type parameters existentially quantified. *)
let exi_quant_param ts sym (f: translation_state -> 'a) (g: symbol -> ttype -> unit) =
    assert (List.for_all (fun (sym', _) -> sym != sym') ts.ts_exi_quants);
    assert (List.for_all (function
        | {sym_kind=Type_param; sym_type=Some _} -> false
        | _ -> true) sym.sym_locals);
    let cleanup () =
        List.iter (function
            | {sym_kind=Type_param; sym_type=Some _} as tp -> tp.sym_type <- None
            | _ -> ()) sym.sym_locals
    in try
        let result = f {ts with ts_exi_quants = (sym, g) :: ts.ts_exi_quants} in
        cleanup (); result
    with e -> cleanup (); raise e

(* Sort binding list into original key order (physical comparison).
   keys - original order of keys
   bindings - list of (key, value) bindings *)
let sort_bindings keys bindings =
    let rec process result = function
        | [], [], [] -> List.rev result
        | [], _, _ -> raise (Failure "sort_bindings (too few keys)")
        | k::keys, checked, (k',v')::remaining when k == k' ->
            process ((k',v')::result) (keys, [], (List.rev_append checked remaining))
        | k::keys, checked, (k',v')::remaining ->
            process result (k::keys, (k',v')::checked, remaining)
        | k::keys, checked, [] ->
            raise (Failure "sort_bindings (too many/wrong keys)")
    in process [] (keys, [], bindings)

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

let rec type_check ts loc t1 t2 =
    match t1, t2 with
        | t1, t2 when t1 == t2 -> () (* short-cut if the types are exactly the same *)
        | No_type, No_type -> ()
        | Pointer_type(t1), Pointer_type(t2) -> type_check ts loc t1 t2
        | Named_type(s1, params1), Named_type(s2, params2) when s1 == s2 ->
            (* Same symbol. Type params must match too. *)
            List.iter2 (fun (param1, t1) (param2, t2) ->
                assert (param1 == param2);
                type_check ts loc t1 t2
            ) params1 params2

        (* Type parameters. *)
        | Named_type({sym_kind=Type_param; sym_type=Some t1}, []), t2
        | t1, Named_type({sym_kind=Type_param; sym_type=Some t2}, []) ->
            (* Apply current substitution. *)
            type_check ts loc t1 t2
        | Named_type({sym_kind=Type_param; sym_type=None} as tp, []), ty
        | ty, Named_type({sym_kind=Type_param; sym_type=None} as tp, []) ->
            let rec search = function
                | [] -> raise Type_mismatch
                | (s,f)::_ when s == tp.sym_parent ->
                    f tp ty;
                    tp.sym_type <- Some ty
                | _::quants -> search quants
            in search ts.ts_exi_quants

        (* Type aliases. *)
        | Named_type({sym_kind=Type_sym; sym_type=Some t1}, []), t2
        | t1, Named_type({sym_kind=Type_sym; sym_type=Some t2}, []) ->
            type_check ts loc t1 t2
        (* Type mismatches. *)
        | No_type, _ | _, No_type
        | Integer_type, _ | _, Integer_type
        | Boolean_type, _ | _, Boolean_type
        | Char_type, _ | _, Char_type
        | Pointer_type _, _ | _, Pointer_type _
        | Named_type _, Named_type _ ->
            raise Type_mismatch

let expect_type ts loc target_type why_target source_type =
    try type_check ts loc target_type source_type
    with Type_mismatch ->
        Errors.semantic_error loc
            ("Type mismatch " ^ why_target ^ ": expected `"
                ^ string_of_type target_type
                ^ "' but got `" ^ string_of_type source_type ^ "'.")

let match_types ts loc t1 t2 =
    try type_check ts loc t1 t2
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
    | Apply(loc, _, _, _)
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
    proc_sym.sym_type <- (match return_type with
        | Some rt -> Some (trans_type ts rt)
        | None -> Some No_type)

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
    | Parse_tree.Proc_decl(loc, name, type_params, params, return_type, maybe_body) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let proc_sym = create_sym ts.ts_scope loc name Proc in
        let disp_tp = trans_type_params {ts with ts_scope = proc_sym} type_params true in
        trans_params ts proc_sym params return_type;
        begin match maybe_body with
            | Some body -> todo ts (Todo_proc(body, proc_sym))
            | None ->
                begin match disp_tp with
                    | Some _ ->
                        todo ts (Todo_abstract_proc proc_sym)
                    | None ->
                        Errors.semantic_error loc
                            ("Non-dispatching procedure cannot be abstract.")
                end;
                proc_sym.sym_abstract <- true
        end
    | Parse_tree.Proc_import(loc, name, type_params, params, return_type) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let proc_sym = create_sym ts.ts_scope loc name Proc in
        let disp_tp = trans_type_params {ts with ts_scope = proc_sym} type_params true in
        ignore disp_tp;
        trans_params ts proc_sym params return_type;
        proc_sym.sym_imported <- true
    | Parse_tree.Proc_override(loc, name, type_params, params, return_type, body) ->
        begin match find_dotted_name ts loc name with
            | {sym_kind=Proc} as base_proc ->
                if not (is_dispatching base_proc) then
                    Errors.semantic_error loc
                        ("Cannot override non-dispatching procedure `"
                            ^ name_for_error ts base_proc ^ "'.");
                let proc_sym = create_sym ts.ts_scope loc "" Proc in
                proc_sym.sym_base_proc <- Some base_proc;
                begin match trans_type_params {ts with ts_scope = proc_sym} type_params true with
                    | None -> ()
                    | Some _ ->
                        Errors.semantic_error loc
                            ("Overriding procedure cannot declare a dispatching type parameter.")
                end;
                trans_params ts proc_sym params return_type;
                (* Check that the overriding procedure is type-compatible with the base procedure. *)
                let base_params = get_params base_proc in
                let ovrd_params = get_params proc_sym in
                if List.length base_params <> List.length ovrd_params then
                    Errors.semantic_error loc
                        ("Overriding procedure has "
                            ^ (if List.length base_params < List.length ovrd_params then "more" else "fewer")
                            ^ " parameters than procedure `"
                            ^ name_for_error ts base_proc ^ "'.")
                else begin
                    List.iter (fun tp -> tp.sym_selected <- false) (get_type_params proc_sym);
                    exi_quant_param ts base_proc (fun ts ->
                        (* Parameter types must be an instance of the base's parameter types. *)
                        List.iter2 (fun base_param ovrd_param ->
                            if base_param.sym_name <> ovrd_param.sym_name then
                                Errors.semantic_error (unsome ovrd_param.sym_defined)
                                    ("Parameter name mismatch: `"
                                        ^ ovrd_param.sym_name ^ "' should be called `"
                                        ^ base_param.sym_name ^ "'.") else
                            (* XXX: Probably need more strictness than coerce. *)
                            expect_type ts (unsome ovrd_param.sym_defined)
                                (unsome base_param.sym_type) "for overriding parameter"
                                (unsome ovrd_param.sym_type)
                        ) base_params ovrd_params;
                        let dispatching_tp = get_dispatching_type_param base_proc in
                        iter_type_params_in (fun tp ->
                            if tp == dispatching_tp then begin
                                (* occurs check fail! *)
                                assert false
                            end else begin
                                if tp.sym_selected then begin
                                    Errors.semantic_error loc
                                        ("Overriding procedure constrains non-dispatching type parameter `"
                                            ^ tp.sym_name ^ "' by overriding with type `"
                                            ^ string_of_type (unsome dispatching_tp.sym_type) ^ "'.")
                                    (* XXX: Say other type parameter name! *)
                                    (* XXX: This is a horrible error message! I barely understand it! *)
                                end
                            end
                        ) (unsome dispatching_tp.sym_type);
                        (* Return type must also be an instance of the base's return type. *)
                        (* XXX: Probably need more strictness than coerce. *)
                        expect_type ts loc (unsome proc_sym.sym_type) "overriding return type"
                            (unsome base_proc.sym_type)
                    ) (fun v t ->
                        assert (v.sym_kind == Type_param);
                        if v.sym_dispatching then begin
                            match t with
                                | Named_type({sym_kind=Type_param; sym_parent=p; sym_name=new_name}, _) when p == proc_sym ->
                                    Errors.semantic_error loc
                                        ("Overriding procedure doesn't specialise dispatching type parameter `" ^ v.sym_name
                                         ^ (if v.sym_name = new_name then "'."
                                            else "', it just renames it to `" ^ new_name ^ "'."))
                                | _ ->
                                    (* Dispatching type parameter is specialised for t. *)
                                    base_proc.sym_overrides <- (proc_sym, t) :: base_proc.sym_overrides
                        end else begin
                            (* Non-dispatching type params can't introduce constraints,
                               so there should be a mapping from overriding type params
                               to base params. *)
                            match t with
                                | Named_type({sym_kind=Type_param; sym_parent=p; sym_name=new_name} as tp, _) when p == proc_sym ->
                                    tp.sym_selected <- true
                                | _ ->
                                    Errors.semantic_error loc
                                        ("Overriding procedure specialises non-dispatching type parameter `"
                                         ^ v.sym_name ^ "'.")
                        end
                    );
                    todo ts (Todo_proc(body, proc_sym))
                end
            | bad_sym -> wrong_sym_kind ts loc bad_sym "dispatching procedure"
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
        let None = trans_type_params {ts with ts_scope = type_sym} type_params false in
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
                        expect_type ts loc specified_type
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

and trans_type_params ts type_params can_dispatch =
    let disp_tp = ref None in
    List.iter (fun (loc, name, dispatching) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let new_param = create_sym ts.ts_scope loc name Type_param in
        match can_dispatch, dispatching, !disp_tp with
            | false, false, _ -> ()
            | false, true, _ ->
                Errors.semantic_error loc
                    ("`disp' only makes sense for procedures, not for types.")
            | true, false, _ -> ()
            | true, true, None ->
                new_param.sym_dispatching <- true;
                disp_tp := Some new_param
            | true, true, Some tp ->
                Errors.semantic_error loc
                    ("Only one type parameter can be marked as dispatching.")
    ) type_params;
    !disp_tp

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
            | bad_sym -> wrong_sym_kind ts loc bad_sym "type"
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
            | Apply(loc, proc, args, tbinds), No_type ->
                emit ts (Call(loc, proc, args, tbinds))
            | Apply(loc, Name(_,({sym_kind=Proc} as proc_sym)), _, _), _ ->
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
        expect_type ts loc dest_type "for assignment" src_type;
        emit ts (Assign(loc, dest, src))
    | Parse_tree.Return(loc, Some e) ->
        begin match ts.ts_scope with
            | {sym_kind=Proc; sym_type=Some No_type} ->
                Errors.semantic_error (loc_of_expr e)
                    ("Procedure `" ^ name_for_error ts ts.ts_scope
                     ^ "' has no return type, so cannot return a value.")
            | {sym_kind=Proc; sym_type=Some t} ->
                let e, e_type, _ = trans_expr ts (Some t) e in
                expect_type ts (loc_of_iexpr e) t ("for returned value") e_type;
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
                expect_type ts loc Boolean_type "for condition" condition_type;
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
        expect_type ts loc Boolean_type "for condition" cond_type;
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
                let tp_bindings = ref [] in
                exi_quant_param ts proc_sym (fun ts ->
                    let matched_args =
                        (* Match arguments to parameters and coerce types. *)
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
                            expect_type ts (loc_of_iexpr arg) (unsome param.sym_type)
                                ("for parameter `" ^ param.sym_name ^ "'") arg_type;
                            (param, arg)
                        ) (match_args_to_params loc "arguments"
                            (get_params proc_sym) pos_args named_args) in
                    (* Sort tp_bindings into original order. *)
                    let tp_bindings = sort_bindings (get_type_params proc_sym) !tp_bindings in
                    todo ts (Todo_apply_check(Apply(loc, proc, matched_args, tp_bindings)));
                    (Apply(loc, proc, matched_args, tp_bindings),
                     follow_tparams (unsome proc_sym.sym_type) (* return type *), false)
                ) (fun v t ->
                    tp_bindings := (v, t) :: !tp_bindings;
                    match t with
                        | Named_type({sym_kind=Type_param} as tp, []) ->
                            (* XXX: There will probably be tp.sym_parent != ts.ts_scope cases in the future. *)
                            assert (tp.sym_parent == ts.ts_scope);
                            tp.sym_dispatched_to <- (v, loc) :: tp.sym_dispatched_to
                        | _ -> ()
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
                expect_type ts loc (unsome field.sym_type)
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
    while !(ts.ts_todo) <> [] do
        let items = !(ts.ts_todo) in
        ts.ts_todo := [];
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
            | _ -> ()
        ) items;
        List.iter (function
            | Todo_proc(stmts, proc_sym) ->
                let stmts' = ref [] in
                trans_stmts {ts with ts_scope = proc_sym;
                                     ts_block = Some stmts'} stmts;
                proc_sym.sym_code <- Some !stmts';
                subs := proc_sym :: !subs;
                proc_sym.sym_translated <- true
            | Todo_abstract_proc proc_sym ->
                subs := proc_sym :: !subs
            | _ -> ()
        ) items;
        List.iter (function
            | Todo_apply_check(Apply(loc, Name(_, ({sym_kind=Proc} as proc_sym)), args, tbinds)) ->
                (* For each type parameter of proc_sym, make sure that all
                   the required dispatching procs are supported. *)
                List.iter (fun tp ->
                    match List.assq tp tbinds with
                        | Named_type({sym_kind=Type_param; sym_parent=p}, []) -> () (* XXX: ? *)
                        | ty ->
                            (* TODO: Find ambiguities! *)
                            List.iter (fun (proc2, hist) ->
                                if is_dispatching proc2 && proc2.sym_abstract then begin
                                    if not (List.exists (fun (ovrd_proc, ty') ->
                                        (* XXX: Need to apply tbinds here? *)
                                        exi_quant_param ts(*?*) ovrd_proc (fun ts ->
                                            try type_check ts loc ty ty'; true
                                            with Type_mismatch -> false
                                        ) (fun _ _ -> ())
                                    ) proc2.sym_overrides) then begin
                                        Errors.semantic_error loc
                                            ("Abstract dispatching procedure `" ^ name_for_error ts proc2
                                             ^ "' must be overridden for type `"
                                             ^ string_of_type ty ^ "'.");
                                        List.iter (fun (tp',loc) ->
                                            Errors.semantic_error loc
                                                ("because " ^ describe_sym tp'.sym_parent
                                                 ^ " `" ^ name_for_error ts tp'.sym_parent
                                                 ^ "' is called here.")
                                        ) (List.rev hist)
                                    end
                                end
                            ) (get_dispatch_list tp)
                ) (get_type_params proc_sym)
            | _ -> ()
        ) items;

    done;
        
    (* XXX: Don't do this here! *)
    let c_state = Codegen_c.new_state () in
    List.iter (Codegen_c.trans_sub c_state) !subs
