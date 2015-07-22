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
    ts_exi_quants: symbol list; (* list of symbols whose type parameters can be unified *)
    ts_subst: (symbol * ttype) list ref; (* list of type parameter substitutions *)
}

let new_translation_state root = {
    ts_root = root;
    ts_scope = root;
    ts_todo = ref [];
    ts_block = None;
    ts_exi_quants = [];
    ts_subst = ref [];
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

(* Call f and return a list of substitutions f made.
   (The substitutions will no longer be active after f returns. *)
let unif_ctx ts (f: translation_state -> 'a): ('a * (symbol * ttype) list) =
    let ts2 = {ts with ts_subst = ref !(ts.ts_subst)} in
    let f_result = f ts2 in
    let rec gather result substs1 substs2 =
        if substs1 == substs2 then result
        else let x::l = substs2 in gather (x::result) substs1 l
    in (f_result, gather [] !(ts.ts_subst) !(ts2.ts_subst))

(* Call f with sym's type parameters existentially quantified. *)
let exi_quant_param ts sym (f: translation_state -> 'a) =
    assert (List.for_all ((!=) sym) ts.ts_exi_quants);
    unif_ctx {ts with ts_exi_quants = sym::ts.ts_exi_quants} f

(* Perform a type parameter substitution. *)
let substitute ts tp ty e =
    assert (not (List.mem_assq tp !(ts.ts_subst))); (* not already substituted *)
    (* can only substitute if allowed *)
    if not (List.memq tp.sym_parent ts.ts_exi_quants) then begin
        (* prerr_endline ("Cannot subst " ^ tp.sym_name ^ " -> " ^ string_of_type ty);
        prerr_endline (String.concat ", " (List.map (fun s -> s.sym_name) ts.ts_exi_quants)); *)
        raise e
    end;
    (* add to current substitutions *)
    ts.ts_subst := (tp, ty)::!(ts.ts_subst)

(* Make bindings active. *)
let activate ts tbinds = ts.ts_subst := tbinds @ !(ts.ts_subst)

(* Sort binding list into original key order (physical comparison).
   keys - original order of keys
   bindings - list of (key, value) bindings, in any order *)
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
    | Pointer_type t -> Pointer_type (subst_tparams tparams t)
    | Named_type({sym_kind=Type_param} as param, []) as ty ->
        begin match maybe_assq param tparams with
            | Some ty -> ty
            | None -> ty
        end
    | Named_type(tsym, tbinds) -> Named_type(tsym, tbinds)

(* Apply current type parameter substitutions. *)
let follow_tparams ts = subst_tparams !(ts.ts_subst)

(* Return the actual type (follow Named_type) *)
let rec actual_type = function
    | (Integer_type | Char_type | Pointer_type _ | Record_type _ | Proc_type _) as t -> t
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

(* if exact is true, only allow alpha renaming *)
let rec type_check ts exact t1 t2 =
    match t1, t2 with
        | t1, t2 when t1 == t2 -> () (* short-cut if the types are exactly the same *)
        | No_type, No_type -> ()
        | Pointer_type(t1), Pointer_type(t2) -> type_check ts exact t1 t2
        | Named_type(s1, params1), Named_type(s2, params2) when s1 == s2 ->
            (* Same symbol. Type params must match too. *)
            List.iter2 (fun (param1, t1) (param2, t2) ->
                assert (param1 == param2);
                type_check ts exact t1 t2
            ) params1 params2

        (* Type parameters. *)
        (* XXX: This is a horrid mess! Tidy it up! *)
        | Named_type({sym_kind=Type_param} as tp1, []),
          Named_type({sym_kind=Type_param} as tp2, []) ->
            (* Type parameters on both sides. *)
            begin match maybe_assq tp1 !(ts.ts_subst) with
                | Some t1 -> type_check ts exact t1 t2 (* apply current substitution to t1 *)
                | None -> match maybe_assq tp2 !(ts.ts_subst) with
                    | Some t2 -> type_check ts exact t1 t2 (* apply current substitution to t2 *)
                    | None ->
                        if List.memq tp2.sym_parent ts.ts_exi_quants then
                            (* perform substitution in the direction that will work
                               e.g. T -> U will fail if T is not in exi_quants
                               but U -> T is still a valid unification. *)
                            substitute ts tp2 t1 Type_mismatch
                        else
                            substitute ts tp1 t2 Type_mismatch
            end
        | Named_type({sym_kind=Type_param} as tp, []), t2 ->
            if exact then raise Type_mismatch else
            begin match maybe_assq tp !(ts.ts_subst) with
                | Some t1 -> type_check ts exact t1 t2 (* apply current substitution *)
                | None -> substitute ts tp t2 Type_mismatch (* substitute to make types match *)
            end
        | t1, Named_type({sym_kind=Type_param} as tp, []) ->
            if exact then raise Type_mismatch else
            begin match maybe_assq tp !(ts.ts_subst) with
                | Some t2 -> type_check ts exact t1 t2 (* apply current substitution *)
                | None -> substitute ts tp t1 Type_mismatch (* substitute to make types match *)
            end

        | Proc_type(s1, []), Proc_type(s2, []) ->
            (* TODO: Handle non-empty tbinds! *)
            (* TODO: Nominal type checking:
                We want to allow implicit conversion from anonymous to a
                compatible function pointer type, but not between named
                function pointer types. *)
            (* TODO: Merge with checking for "implements" *)
            (* TODO: Unify type parameters etc.! Requires trampolines oh no! *)
            let params1 = get_params s1 in
            let params2 = get_params s2 in
            if (List.length params1) <> (List.length params2) then raise Type_mismatch
            else begin
                List.iter2 (fun param1 param2 ->
                    (* TODO: Check parameter names! *)
                    type_check ts exact (unsome param1.sym_type) (unsome param2.sym_type)
                ) params1 params2;
                type_check ts exact (unsome s1.sym_type) (unsome s2.sym_type) (* return types *)
            end

        (* Type aliases. *)
        | Named_type({sym_kind=Type_sym; sym_type=Some t1}, []), t2
        | t1, Named_type({sym_kind=Type_sym; sym_type=Some t2}, []) ->
            type_check ts exact t1 t2
        (* Type mismatches. *)
        | No_type, _ | _, No_type
        | Integer_type, _ | _, Integer_type
        | Boolean_type, _ | _, Boolean_type
        | Char_type, _ | _, Char_type
        | Pointer_type _, _ | _, Pointer_type _
        | Named_type _, Named_type _ ->
            raise Type_mismatch

(* Check function symbol fsym2 is an instance of fsym1. *)
let check_func_is_instance ts loc fsym1 fsym2 =
    let (), _ = exi_quant_param ts fsym1 (fun ts ->
        let params1 = get_params fsym1 in
        let params2 = get_params fsym2 in
        if List.length params1 <> List.length params2 then begin
            Errors.semantic_error loc
                (String.capitalize (describe_sym fsym2) ^ " `" ^ name_for_error ts fsym2 ^ "' has "
                    ^ string_of_int (List.length params2) ^ " parameter(s), but...");
            Errors.semantic_error (unsome fsym1.sym_defined)
                ("..." ^ describe_sym fsym1 ^ " `" ^ name_for_error ts fsym1 ^ "' has "
                    ^ string_of_int (List.length params1) ^ ".");
            raise Errors.Compile_error
        end;
        (* TODO: Better matching for errors? (Try to find one with correct name on name mismatch, etc. *)
        List.iter2 (fun param1 param2 ->
            begin try type_check ts false (unsome param1.sym_type) (unsome param2.sym_type)
            with Type_mismatch ->
                Errors.semantic_error loc ("Parameter `" ^ param2.sym_name ^ "' of " ^ describe_sym fsym2 ^ " `"
                    ^ name_for_error ts fsym2 ^ "' has type `"
                    ^ string_of_type (unsome param2.sym_type) ^ "', but...");
                Errors.semantic_error (unsome param1.sym_defined) ("parameter `"
                    ^ param1.sym_name ^ "' of " ^ describe_sym fsym1 ^ " `"
                    ^ name_for_error ts fsym1 ^ "' has type `" ^ string_of_type (unsome param1.sym_type) ^ "'.");
                raise Errors.Compile_error
            end
            (* TODO: Check names -> issue a warning? *)
        ) params1 params2
    ) in ()

let expect_type ts loc target_type why_target source_type =
    try type_check ts false target_type source_type
    with Type_mismatch ->
        Errors.semantic_error loc
            ("Type mismatch " ^ why_target ^ ": expected `"
                ^ string_of_type target_type
                ^ "' but got `" ^ string_of_type source_type ^ "'.")

let match_types ts loc t1 t2 =
    try type_check ts false t1 t2
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
    | Name(loc, _)
    | Int_literal(loc, _)
    | String_literal(loc, _)
    | Char_literal(loc, _)
    | Apply(loc, _, _, _, _)
    | Record_cons(loc, _, _)
    | Field_access(loc, _, _)
    | Binop(loc, _, _, _)
    | Deref(loc, _)
    | New(loc, _, _)
        -> loc
    | Genericify(e,_) -> loc_of_iexpr e

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

    (* Class declaration *)
    | Parse_tree.Class_decl(loc, name, type_params, items) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let cls = create_sym ts.ts_scope loc name Class in
        trans_type_params {ts with ts_scope = cls} type_params;
        todo ts Todo_class (fun () ->
            List.iter (function
                | Parse_tree.Class_proc(loc, name, constr_type_params, params, return_type) ->
                    check_for_duplicate_definition cls loc name;
                    let cls_proc = create_sym cls loc name Class_proc in
                    trans_constrained_type_params {ts with ts_scope = cls} constr_type_params;
                    trans_params ts cls_proc params return_type
            ) items
        )

    (* Procedure definition *)
    | Parse_tree.Proc_decl(loc, name, constr_type_params, params, return_type, maybe_implements, body) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        let proc_sym = create_sym ts.ts_scope loc name Proc in
        trans_constrained_type_params {ts with ts_scope = proc_sym} constr_type_params;
        trans_params ts proc_sym params return_type;
        todo ts Todo_proc (fun () ->
            begin match maybe_implements with
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
            end;

            let stmts = ref [] in
            trans_stmts {ts with ts_scope = proc_sym;
                                 ts_block = Some stmts} body;
            proc_sym.sym_code <- Some !stmts;
            proc_sym.sym_translated <- true
        )

    | Parse_tree.Proc_import(loc, name, constr_type_params, params, return_type, maybe_implements, c_name) ->
        (* TODO: There is much in common with Proc_decl: merge! *)
        check_for_duplicate_definition ts.ts_scope loc name;
        let proc_sym = create_sym ts.ts_scope loc name Proc in
        trans_constrained_type_params {ts with ts_scope = proc_sym} constr_type_params;
        trans_params ts proc_sym params return_type;
        proc_sym.sym_imported <- Some c_name;
        todo ts Todo_proc (fun () ->
            begin match maybe_implements with
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
            end
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
        trans_type_params {ts with ts_scope = type_sym} type_params;
        type_sym.sym_type <- Some (Record_type(None)); (* TODO: base record *)
        todo ts Todo_type (fun () ->
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

and trans_type_params ts =
    List.iter (fun (loc, name) ->
        check_for_duplicate_definition ts.ts_scope loc name;
        ignore (create_sym ts.ts_scope loc name Type_param)
    )

and trans_constrained_type_params ts (type_params, tconstraints) =
    trans_type_params ts type_params;
    ts.ts_scope.sym_tconstraints <- List.map (fun (loc, class_name, (pos_args, named_args)) ->
        match find_dotted_name ts loc class_name with
            | ({sym_kind=Class} as cls), [] ->
                (cls, List.map (fun (param, arg) ->
                        (param, trans_type ts arg))
                    (match_args_to_params loc "class arguments"
                        (get_type_params cls) pos_args named_args))
            | bad_sym, _ -> wrong_sym_kind ts loc bad_sym "class"
    ) tconstraints

and trans_type ts = function
    | Parse_tree.Integer_type -> Integer_type
    | Parse_tree.Boolean_type -> Boolean_type
    | Parse_tree.Char_type -> Char_type
    | Parse_tree.Named_type(loc, [name]) ->
        begin match search_scopes_or_fail ts loc name with
            | {sym_kind=Type_sym} as typ, [] ->
                Named_type(typ, [])
            | {sym_kind=Type_param} as typ_p, [] ->
                Named_type(typ_p, [])
            | bad_sym, _ -> wrong_sym_kind ts loc bad_sym "type"
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
    | Parse_tree.Proc_type(loc, constr_type_params, params, return_type) ->
        let ptypesym = create_sym ts.ts_scope loc "" Proc_type_sym in
        trans_constrained_type_params {ts with ts_scope = ptypesym} constr_type_params;
        trans_params ts ptypesym params return_type;
        Proc_type(ptypesym, [])
        


and trans_stmts ts = List.iter (trans_stmt ts)

and trans_stmt ts = function
    | Parse_tree.Decl decl -> trans_decl ts decl
    | Parse_tree.Expr((Parse_tree.Apply _) as e) ->
        let call, tcall, _ = trans_expr ts None e in
        begin match call, tcall with
            | Apply(loc, proc, args, tbinds, classes), No_type ->
                emit ts (Call(loc, proc, args, tbinds, classes))
            | Apply(loc, Name(_,({sym_kind=Proc} as proc_sym)), _, _, _), _ ->
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
                    Right(Name(loc, sym), Proc_type(sym, []), false, unsome sym.sym_defined)
        in

        (* Search for first part of name. *)
        let rec find_name_start scope results =
            (* Search locals. *)
            let results = match maybe_find (fun s -> s.sym_name = name_start) scope.sym_locals with
                | Some sym -> (result_of_sym loc sym)::results
                | None -> results in
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
                                | Named_type({sym_kind=Type_sym; sym_type=Some(Record_type _)} as type_sym, tparams) ->
                                    begin match maybe_find (fun s -> s.sym_name = name) (get_fields type_sym) with
                                        | Some field ->
                                            follow_name_tail (Right(Field_access(loc, expr, field),
                                                  subst_tparams tparams (unsome field.sym_type), lvalue, unsome field.sym_defined)) name_tail
                                        | None ->
                                            Errors.semantic_error loc
                                                ("Type `" ^ name_for_error ts type_sym ^ "' has no field named `"
                                                    ^ name ^ "'.");
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
            | Named_type({sym_kind=Type_sym; sym_type=Some(Record_type _)} as type_sym, tparams) ->
                begin match maybe_find (fun s -> s.sym_name = name) (get_fields type_sym) with
                    | Some field ->
                        (Field_access(loc, e, field), subst_tparams tparams (unsome field.sym_type), lv)
                    | None ->
                        Errors.semantic_error loc
                            ("Type `" ^ name_for_error ts type_sym ^ "' has no field named `"
                                ^ name ^ "'.");
                        raise Errors.Compile_error
                end
            | wrong_type ->
                Errors.semantic_error loc
                    ("Type `" ^ string_of_type ty ^ "' has no fields.");
                raise Errors.Compile_error
        end
    | Parse_tree.Int_literal(loc, n) ->
        (Int_literal(loc, n), Integer_type, false)
    | Parse_tree.String_literal(loc, s) ->
        (String_literal(loc, s), Pointer_type(Char_type), false)
    | Parse_tree.Char_literal(loc, s) ->
        (Char_literal(loc, s), Char_type, false)
    | Parse_tree.Apply(loc, proc, (pos_args, named_args)) ->
        let proc, proc_type, _ = trans_expr ts None proc in
        begin match actual_type proc_type with
            | Proc_type(proc_sym, tbinds) ->
                (* proc_sym is either a Proc symbol or a Proc_type Type_sym symbol. *)
                let matched_args, tbinds = exi_quant_param ts proc_sym (fun ts ->
                    activate ts tbinds;
                    (* Match arguments to parameters and coerce types
                       (thus substituting the callee's type parameters). *)
                    List.map (fun (param, arg) ->
                        let param_type = unsome param.sym_type in
                        let arg, arg_type, lvalue = trans_expr ts (Some param_type) arg in
                        let arg = match param_type, arg_type with
                            | Named_type({sym_kind=Type_param},[]), Named_type({sym_kind=Type_param},[]) -> arg
                            | Named_type({sym_kind=Type_param},[]), _ ->
                                (* Back-end might need to know that this value becomes generic at this point. *)
                                Genericify(arg, arg_type)
                            | _ -> arg in
                        begin match param.sym_param_mode with
                            | Var_param | Out_param ->
                                if not lvalue then begin
                                    Errors.semantic_error (loc_of_iexpr arg)
                                        ("Cannot assign to this expression (parameter `"
                                            ^ param.sym_name ^ "' is declared `"
                                            ^ (match param.sym_param_mode with Var_param -> "var"
                                                                             | Out_param -> "out") ^ "'.")
                                end
                            | Const_param -> ()
                        end;
                        expect_type ts (loc_of_iexpr arg) (unsome param.sym_type)
                            ("for parameter `" ^ param.sym_name ^ "'") arg_type;
                        (param, arg)
                    ) (match_args_to_params loc "arguments"
                        (get_params proc_sym) pos_args named_args)
                ) in
                let return_type = subst_tparams tbinds (unsome proc_sym.sym_type) in
                let classes = ref [] in
                let expr = Apply(loc, proc, matched_args, tbinds, classes) in
                todo ts Todo_apply_check (fun () ->
                    classes := List.map (fun (cls, cls_args) ->
                        (* Can we find a class to pass on to the callee? *)
                        match maybe_find (fun (i, (cls', cls_args')) ->
                            try ignore (unif_ctx ts (fun ts ->
                                activate ts (List.map (fun (tp, ty) -> (tp, subst_tparams tbinds ty)) cls_args);
                                activate ts cls_args';
                                List.iter2 (fun tp tp' ->
                                    type_check ts true (Named_type(tp, [])) (Named_type(tp, []))
                                ) (get_type_params cls) (get_type_params cls')
                            )); true with Type_mismatch -> false
                        ) ( (* Look in current scope's constraints for classes to look at. *)
                            enumerate ts.ts_scope.sym_tconstraints )
                        with
                            | Some (i, _) -> Forward i
                            | None ->
                                (* Cannot forward - must implement the class ourself. *)
                                fst (unif_ctx ts (fun ts ->
                                    (* Substitute class arguments. *)
                                    activate ts (List.map (fun (tp, ty) -> (tp, subst_tparams tbinds ty)) cls_args);
                                    (* Check all class procs. *)
                                    Implement(cls, List.map (fun cls_proc ->
                                        (* Find implementation candidates.
                                           TODO: Proper scope rules! *)
                                        let cls_params = get_params cls_proc in
                                        let candidates = List.fold_left (fun candidates impl ->
                                            let impl_params = get_params impl in
                                            try
                                                ignore (exi_quant_param ts impl (fun ts ->
                                                    List.iter2 (fun cls_param impl_param ->
                                                        prerr_endline ("Checking " ^ string_of_type (unsome cls_param.sym_type)
                                                            ^ " against " ^ string_of_type (unsome impl_param.sym_type));
                                                        type_check ts false
                                                            (unsome cls_param.sym_type)
                                                            (unsome impl_param.sym_type)
                                                    ) cls_params impl_params;
                                                    type_check ts false
                                                        (unsome cls_proc.sym_type)
                                                        (unsome impl.sym_type)
                                                ));
                                                (impl (*, instantiation*))::candidates
                                            with Type_mismatch -> candidates
                                        ) [] cls_proc.sym_implementations in
                                        (* TODO: Eliminate more general candidates. *)
                                        match candidates with
                                            | [] ->
                                                Errors.semantic_error loc
                                                    ("No implementation of `"
                                                        ^ name_for_error ts cls_proc ^ "' found.");
                                                raise Errors.Compile_error
                                            | _::_::_ ->
                                                Errors.semantic_error loc
                                                    ("Multiple implementations of `"
                                                        ^ name_for_error ts cls_proc ^ "' match the types.");
                                                List.iter (fun candidate ->
                                                    Errors.semantic_error (unsome candidate.sym_defined)
                                                        ("`" ^ name_for_error ts candidate ^ "' matches.")
                                                ) candidates;
                                                raise Errors.Compile_error
                                            | [impl (*, instantiation*)] ->
                                                (cls_proc, impl)
                                    ) (List.filter (is_kind Class_proc) cls.sym_locals))
                                ))
                    ) proc_sym.sym_tconstraints
                );
                (expr, return_type, false)
        end
    | Parse_tree.Record_cons(loc, (pos_fields, named_fields)) ->
        (* Get record type from context. *)
        let rec_sym, tbinds = match target_type with
            | Some(Named_type({sym_type=Some(Record_type _)} as sym, tbinds)) -> sym, tbinds
            | Some t -> Errors.semantic_error loc
                ("Value of type `" ^ string_of_type t
                    ^ "' expected but record constructor found.");
                raise Errors.Compile_error
            | None -> Errors.semantic_error loc
                ("Record type cannot be determined by context.");
                raise Errors.Compile_error
        in
        fst (unif_ctx ts (fun ts ->
            activate ts tbinds;
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
             ), unsome target_type, false)
        ))
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
    | Parse_tree.New(loc, e) ->
        let e, ty, lv = trans_expr ts
            (match target_type with
                | None -> None
                | Some(Pointer_type ty) -> Some ty
                | Some ty ->
                    Errors.semantic_error loc
                        ("Value of type " ^ string_of_type ty
                            ^ "' expected but `new' found.");
                    raise Errors.Compile_error
            ) e in
        (New(loc, ty, e), Pointer_type ty, false)

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
    let c_state = Codegen_c.new_state ts.ts_root in
    List.iter (Codegen_c.translate c_state)
        (List.filter (is_kind Proc) unit.sym_locals)
