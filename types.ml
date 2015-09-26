open Symtab
open Misc

type situation =
    | SVar_init of symbol
    | SCall_none
    | SAssign
    | SReturn_stat
    | SCondition
    | SApply of symbol option
    | SParameter of proc_param
    | SReturn_type
    | SRecord_cons
    | SBoolean_op
    | SBinop
    | SField of record_field

type reason =
    | EField_count of record_type * record_type
    | EField_order of record_field * record_field
    | EParam_mode of proc_param * proc_param
    | EParam_count of proc_type * proc_type
    | EParam_missing_left of proc_param
    | EParam_missing_right of proc_param
    | ESimply_wrong of ttype * ttype

type type_error = situation list * reason

exception Type_mismatch of type_error

type tconstraint =
    | Coerce of ttype * ttype

type context = {
    mutable tc_constraints: tconstraint list;
}

let new_context () =
    { tc_constraints = [] }

let bind v t =
    match v.tvar_link with
        | None ->
            (* TODO: occurs check *)
            v.tvar_link <- Some t
        | Some t' ->
            raise (Failure "bind")

let rec subst v t' t =
    match t with
        | TNone | TBoolean | TInteger | TChar | TName _ -> t
        | TVar v' when v == v' -> t'
        | TPointer t -> TPointer(subst v t' t)
        | TRecord record ->
            TRecord { record with
                      rec_fields = List.map
                        (fun field ->
                            { field with field_type = subst v t' field.field_type }
                        ) record.rec_fields }
        | TProc proc ->
            TProc { proc with
                    proc_params = List.map
                      (fun param -> { param with param_type = subst v t' param.param_type }
                      ) proc.proc_params;
                    proc_return = subst v t' proc.proc_return }

let rec coerce_params ctx sits param1 param2 =
    let bad () = raise (Type_mismatch (sits, EParam_mode(param1, param2))) in
    begin match param1.param_mode, param2.param_mode with
        | Const_param, Const_param -> ()
        | Const_param, Var_param -> ()
        | Const_param, Out_param -> bad ()
        | Var_param, Const_param -> bad ()
        | Var_param, Var_param -> ()
        | Var_param, Out_param -> bad ()
        | Out_param, Const_param -> bad ()
        | Out_param, Var_param -> bad ()
        | Out_param, Out_param -> ()
    end;
    param2.param_mode <- param1.param_mode; (* XXX: Dodgy! *)
    coerce ctx (SParameter(param1)::sits) param2.param_type param1.param_type

and coerce ctx sits t1 t2 =
    match t1, t2 with
        | TNone, TNone -> ()
        | TBoolean, TBoolean -> ()
        | TInteger, TInteger -> ()
        | TChar, TChar -> ()
        | TVar {tvar_link=Some t1}, t2 -> coerce ctx sits t1 t2
        | t1, TVar {tvar_link=Some t2} -> coerce ctx sits t1 t2
        | TVar v, t2 -> bind v t2
        | t1, TVar v -> bind v t1
        | TName s1, TName s2 when s1 == s2 -> ()
        | TName {sym_kind=Type_sym; sym_type=Some t1'}, t2 -> coerce ctx sits t1' t2
        | t1, TName {sym_kind=Type_sym; sym_type=Some t2'} -> coerce ctx sits t1 t2'
        | TPointer t1, TPointer t2 -> coerce ctx sits t1 t2
        | TRecord rec1, TRecord rec2 ->
            if List.length rec1.rec_fields <> List.length rec2.rec_fields then
                raise (Type_mismatch (sits, EField_count(rec1, rec2)));
            List.iter2 (fun field1 field2 ->
                if field1.field_name <> field2.field_name then
                    raise (Type_mismatch (sits, EField_order(field1, field2)));
                coerce ctx (SField(field2)::sits) field1.field_type field2.field_type
            ) rec1.rec_fields rec2.rec_fields
        | TProc proc1, TProc proc2 ->
            let params1 = ref proc1.proc_params in
            let doing_positional = ref true in
            List.iter (fun param2 ->
                match param2.param_name with
                    | None ->
                        assert !doing_positional;
                        begin match !params1 with
                            | [] -> raise (Type_mismatch (sits, EParam_count(proc1, proc2)))
                            | param1::tail ->
                                params1 := tail;
                                coerce_params ctx sits param1 param2
                        end
                    | Some name2 ->
                        doing_positional := false;
                        let rec find head = function
                            | [] -> raise (Type_mismatch (sits, EParam_missing_left(param2)))
                            | param1::tail when param1.param_name = Some name2 ->
                                params1 := List.rev head @ tail;
                                param1
                            | param1::tail ->
                                find (param1::head) tail
                        in
                        let param1 = find [] !params1 in
                        coerce_params ctx sits param1 param2
            ) proc2.proc_params;
            if !params1 <> [] then raise (Type_mismatch (sits, EParam_missing_right(List.hd !params1)));
            coerce ctx (SReturn_type::sits) proc1.proc_return proc2.proc_return
        | TUniv(v, t1), t2 ->
            let v' = new_tvar v.tvar_loc v.tvar_name in
            coerce ctx sits (subst v (TVar v') t1) t2
        | _ -> raise (Type_mismatch(sits, ESimply_wrong(t1, t2)))
