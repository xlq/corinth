open Symtab
open Misc

exception Type_mismatch

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
        | TPointer t -> subst v t' t
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

let rec coerce ctx t1 t2 =
    match t1, t2 with
        | TBoolean, TBoolean -> ()
        | TInteger, TInteger -> ()
        | TChar, TChar -> ()
        | TName s1, TName s2 when s1 == s2 -> ()
        | TName {sym_kind=Type_sym; sym_type=Some t1'}, t2 -> coerce ctx t1' t2
        | t1, TName {sym_kind=Type_sym; sym_type=Some t2'} -> coerce ctx t1 t2'
        | TVar {tvar_link=Some t1}, t2 -> coerce ctx t1 t2
        | t1, TVar {tvar_link=Some t2} -> coerce ctx t1 t2
        | TVar v, t2 -> bind v t2
        | t1, TVar v -> bind v t1
        | TPointer t1, TPointer t2 -> coerce ctx t1 t2
        | TRecord rec1, TRecord rec2 ->
            if List.length rec1.rec_fields <> List.length rec2.rec_fields then raise Type_mismatch;
            List.iter2 (fun field1 field2 ->
                if field1.field_name <> field2.field_name then raise Type_mismatch;
                coerce ctx field1.field_type field2.field_type
            ) rec1.rec_fields rec2.rec_fields
        | TProc proc1, TProc proc2 ->
            if List.length proc1.proc_params <> List.length proc2.proc_params then raise Type_mismatch;
            List.iter2 (fun param1 param2 ->
                if param1.param_name <> param2.param_name then raise Type_mismatch;
                if param1.param_mode <> param2.param_mode then raise Type_mismatch;
                coerce ctx param1.param_type param2.param_type
            ) proc1.proc_params proc2.proc_params;
            coerce ctx proc2.proc_return proc1.proc_return
        | TUniv(v, t1), t2 ->
            let v' = new_tvar v.tvar_origin in
            coerce ctx (subst v (TVar v') t1) t2
