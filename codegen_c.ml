open Big_int
open Symtab
open Misc

type state = {
    s_output: out_channel;
    s_indent: int;
}

let emit s line = output_string s.s_output (times s.s_indent "    " ^ line ^ "\n")

let indent s = {s with s_indent = s.s_indent + 1}

let new_state () =
    let s = {
        s_output = stdout;
        s_indent = 0;
    } in
    emit s "#include <stdbool.h>";
    emit s "#include \"rt/dispatch.h\"";
    emit s "";
    s

let rec dotted_name_of_sym sym =
    if sym.sym_parent == sym then []
    else dotted_name_of_sym sym.sym_parent @ [sym.sym_name]

let c_name_of_dotted_name parts =
    String.concat "__" (List.map String.lowercase parts)

let c_name_of_local sym = String.lowercase sym.sym_name

let rec mangle_type = function
    | Boolean_type -> "bool"
    | Integer_type -> "int"
    | Char_type -> "char"
    | Named_type({sym_kind=Type_sym} as type_sym, targs) ->
        type_sym.sym_name ^ "__"
            ^ String.concat "__" (List.map mangle_type (List.map snd targs))
    | Named_type({sym_kind=Type_param} as tp, []) ->
        c_name_of_type_param tp
    | Pointer_type(t) -> "P" ^ mangle_type t
    | t -> raise (Failure ("cannot mangle `" ^ string_of_type t ^ "'."))

and c_name_of_sym sym =
    match sym with
        | {sym_kind=Proc; sym_imported=true} -> sym.sym_name
        | {sym_kind=Proc; sym_base_proc=Some base_proc} ->
            assert (sym.sym_name = "");
            c_name_of_sym sym.sym_parent ^ "__" ^ String.lowercase base_proc.sym_name
            ^ "__FOR__" ^ mangle_type (List.assq sym base_proc.sym_overrides)
        | _ -> c_name_of_dotted_name (dotted_name_of_sym sym)

and c_name_of_type_sym sym =
    match sym with
        | {sym_kind=Type_sym; sym_type=Some (Record_type _)} ->
            "struct " ^ c_name_of_sym sym
        | {sym_kind=Type_sym; sym_type=Some t} ->
            c_name_of_type t

and c_name_of_type = function
    | Boolean_type -> "bool"
    | Integer_type -> "int"
    | Char_type -> "char"
    | Named_type({sym_kind=Type_sym} as type_sym, _) -> c_name_of_type_sym type_sym
    | Named_type({sym_kind=Type_param}, []) -> "void"
    | Pointer_type(t) -> c_name_of_type t ^ "*"

and c_name_of_var sym =
    match sym.sym_kind with
        | Proc -> c_name_of_sym sym
        | Var ->
            begin match sym.sym_parent.sym_kind with
                | Proc -> c_name_of_local sym (* local variable *)
                | Unit -> c_name_of_sym sym   (* global variable *)
            end
        | Param -> c_name_of_local sym

and c_name_of_type_param tp = "TP" ^ c_name_of_local tp

(*let c_name_of_vtable t = "VTABLE__" ^ mangle_type t*)

let rec is_scalar = function
    | Boolean_type -> true
    | Char_type -> true
    | Integer_type -> true
    | Record_type _ -> false
    | Named_type({sym_kind=Type_sym; sym_type=Some t}, _) -> is_scalar t
    | Named_type({sym_kind=Type_param}, []) -> false
    | Pointer_type _ -> true

let is_param_by_value param_sym =
    match param_sym.sym_param_mode with
        | Var_param | Out_param -> false
        | Const_param -> is_scalar (unsome param_sym.sym_type)

let func_prototype s proc_sym =
    (match proc_sym.sym_type with
        | Some No_type -> "void"
        | Some t -> c_name_of_type t)
    ^ " " ^ c_name_of_sym proc_sym ^ "("
    ^ String.concat ", "
        (List.map (fun tp ->
            (* Type parameters pass type information. *)
            "co_vptr " ^ c_name_of_type_param tp
         ) (get_type_params proc_sym)
         @ List.map (fun param ->
            c_name_of_type (unsome param.sym_type)
            ^ " " ^ (if is_param_by_value param then "" else "*")
            ^ c_name_of_local param
         ) (get_params proc_sym))
    ^ ")"

(* Return the function pointer type for this dispatching procedure
   with the dispatching type parameter omitted. *)
(* XXX: This is very similar to the above. *)
let disp_func_ptr_type s proc_sym =
    "(" ^ (match proc_sym.sym_type with
        | Some No_type -> "void"
        | Some t -> c_name_of_type t)
    ^ " (*)(" ^ String.concat ", "
        (List.map (fun tp -> "co_vptr")
         (List.filter (fun tp -> not tp.sym_dispatching) (get_type_params proc_sym))
         @ List.map (fun param ->
            c_name_of_type (unsome param.sym_type)
            ^ (if is_param_by_value param then "" else "*")) (get_params proc_sym))
    ^ "))"

let rec trans_istmt s = function
    | Call(loc, proc_e, args, tbinds) ->
        emit s (trans_iexpr s (Apply(loc, proc_e, args, tbinds)) ^ ";")
    | Assign(loc, dest, src) ->
        emit s (trans_iexpr s dest ^ " = " ^ trans_iexpr s src ^ ";")
    | Return(loc, None) ->
        emit s ("return;")
    | Return(loc, Some e) ->
        emit s ("return " ^ trans_iexpr s e ^ ";")
    | If_stmt(if_parts, else_part) ->
        List.iter (fun (loc, cond, body) ->
            emit s ("if (" ^ trans_iexpr s cond ^ "){");
            trans_istmts (indent s) body;
        ) if_parts;
        begin match else_part with
            | None -> ()
            | Some (loc, body) ->
                emit s ("} else {");
                trans_istmts (indent s) body;
        end;
        emit s "}"
    | While_stmt(loc, cond, body) ->
        emit s ("while (" ^ trans_iexpr s cond ^ "){");
        trans_istmts (indent s) body;
        emit s "}"

and trans_istmts s = List.iter (trans_istmt s)

and trans_iexpr s = function
    | Name(loc, ({sym_kind=Param} as sym)) ->
        if is_param_by_value sym then
            c_name_of_var sym
        else
            "(*" ^ c_name_of_var sym ^ ")"
    | Name(loc, {sym_kind=Const; sym_const=Some e}) ->
        trans_iexpr s e
    | Name(loc, sym) ->
        c_name_of_var sym
    | Int_literal(loc, n) ->
        string_of_big_int n
    | String_literal(loc, s) ->
        "\"" ^ s ^ "\""
    | Char_literal(loc, s) ->
        "'" ^ s ^ "'"
    | Apply(loc, proc_e, args, tbinds) ->
        begin (* for debugging *)
            match proc_e with Name(_,{sym_kind=Proc;sym_locals=l}) ->
                List.iter (function
                    | {sym_kind=Type_param} as tp ->
                        emit s ("/* " ^ tp.sym_name ^ " dispatches to: "
                          ^ String.concat ", " (List.map (fun (proc,_) -> proc.sym_name) (get_dispatch_list tp)) ^ " */")
                    | _ -> ()) l
        end;

        (* Is this a dispatch site? *)
        let tbinds, proc_e' =
            match proc_e with
                | Name(_,({sym_kind=Proc} as proc_sym)) ->
                    begin match maybe_find (fun (tp, ty) -> tp.sym_dispatching) tbinds with
                        | None -> (* not dispatching *)
                            tbinds, trans_iexpr s proc_e
                        | Some (disp_tp, Named_type({sym_kind=Type_param} as rx_tp, [])) ->
                            (* This is a dispatch site. Remove the dispatching type parameter
                               from tbinds, because it's not passed as a parameter, it's
                               used in the dispatch. *)
                            (List.filter (fun (tp, ty) -> tp != disp_tp) tbinds),
                                ("(" ^ disp_func_ptr_type s proc_sym
                                 ^ " co_dispatch(" ^ c_name_of_type_param rx_tp
                                 ^ ", (co_unkfn) &" ^ c_name_of_sym proc_sym
                                 ^ "))")
                        | Some (disp_tp, ty) ->
                            (* Static dispatch. *)
                            raise (Failure "TODO: Static dispatch")
                    end
                | _ -> tbinds, trans_iexpr s proc_e
        in
        proc_e' ^ "("
        ^ String.concat ", "
            (List.map (fun (tp, t) ->
                match t with
                    | Named_type({sym_kind=Type_param} as tp, []) ->
                        c_name_of_type_param tp
                    | t -> 
                        "(co_disp_ent[]){" ^ TODO TODO TODO c_name_of_vtable t
             ) tbinds (* XXX: This assumes tbinds are in order! *)
             @ List.map (fun (param, arg) ->
            (if is_param_by_value param then trans_iexpr s arg
            else "&(" ^ trans_iexpr s arg ^ ")")) args) ^ ")"
    | Binop(loc, lhs, op, rhs) ->
        "(" ^ trans_iexpr s lhs ^ ") "
            ^ (match op with
                | Add -> "+"
                | Subtract -> "-"
                | Multiply -> "*"
                | Divide -> "/"
                | LT -> "<"
                | GT -> ">"
                | LE -> "<="
                | GE -> ">="
                | EQ -> "=="
                | NE -> "!=")
            ^ " (" ^ trans_iexpr s rhs ^ ")"
    | Record_cons(loc, rec_sym, fields) ->
        "(" ^ c_name_of_type_sym rec_sym ^ "){" ^
            String.concat ", " (List.map (fun (field, value) ->
                trans_iexpr s value) fields) ^ "}"
    | Field_access(loc, lhs, field) ->
        (trans_iexpr s lhs) ^ "." ^ c_name_of_local field
    | Deref(loc, ptr) ->
        "*(" ^ trans_iexpr s ptr ^ ")"

let rec declare s complete sym =
    if sym.sym_backend_translated < (if complete then 2 else 1) then begin
        if complete then declare_prerequisites s sym;
        match sym with
            | {sym_kind=Type_sym; sym_type=Some(Record_type None)} as type_sym ->
                if complete then begin
                    type_sym.sym_backend_translated <- 2;
                    emit s (c_name_of_type_sym type_sym ^ " {");
                    begin let s = indent s in
                        List.iter (function
                            | {sym_kind=Type_param} -> ()
                            | {sym_kind=Var} as field ->
                                emit s (c_name_of_type (unsome field.sym_type)
                                    ^ " " ^ c_name_of_local field ^ ";")
                        ) type_sym.sym_locals
                    end;
                    emit s "};";
                    emit s ""
                end else begin
                    type_sym.sym_backend_translated <- 1;
                    emit s (c_name_of_type_sym type_sym ^ ";") (* "struct foo;" *)
                end
            | {sym_kind=Type_sym; sym_type=Some t} as type_sym ->
                declare_type s true t;
                type_sym.sym_backend_translated <- 1
            | {sym_kind=Proc} as proc_sym ->
                emit s (func_prototype s proc_sym ^ ";");
                proc_sym.sym_backend_translated <- 1
            | {sym_kind=Var|Param} -> ()
    end

and declare_type s complete = function
    | No_type -> ()
    | Pointer_type(t) ->
        declare_type s false t
    | Boolean_type -> ()
    | Integer_type -> ()
    | Char_type -> ()
    | Named_type({sym_kind=Type_param}, []) -> ()
    | Named_type({sym_kind=Type_sym} as type_sym, _) -> declare s complete type_sym

and declare_prerequisites s = function
    | {sym_kind=Type_sym; sym_type=Some(Record_type None)} as type_sym ->
        List.iter (function
            | {sym_kind=Type_param} -> ()
            | {sym_kind=Var} as field ->
                declare_type s true (unsome field.sym_type)
        ) type_sym.sym_locals
    | {sym_kind=Type_sym; sym_type=Some t} ->
        declare_type s true t
    | {sym_kind=Var|Param} as var_sym ->
        declare_type s true (unsome var_sym.sym_type)
    | {sym_kind=Type_param} -> ()
    | {sym_kind=Proc} as proc_sym ->
        declare_type s true (unsome proc_sym.sym_type);
        List.iter (declare_prerequisites s) proc_sym.sym_locals;
        if not proc_sym.sym_imported then
            match proc_sym.sym_code with
                | None -> ()
                | Some stmts -> List.iter (declare_prereq_stmt s) stmts

and declare_prereq_stmt s = function
    | Call(loc, f, args, tbinds) ->
        declare_prereq_expr s (Apply(loc, f, args, tbinds))
    | Assign(loc, a, b) ->
        declare_prereq_expr s a;
        declare_prereq_expr s b
    | Return(loc, Some e) -> declare_prereq_expr s e
    | Return(loc, None) -> ()
    | If_stmt(bits, else_part) ->
        List.iter (fun (loc, cond, body) ->
            declare_prereq_expr s cond;
            List.iter (declare_prereq_stmt s) body
        ) bits;
        begin match else_part with
            | Some(loc, body) ->
                List.iter (declare_prereq_stmt s) body
            | None -> ()
        end
    | While_stmt(loc, cond, body) ->
        declare_prereq_expr s cond;
        List.iter (declare_prereq_stmt s) body

and declare_prereq_expr s = function
    | Name(loc, sym) -> declare s false sym
    | Int_literal _ -> ()
    | String_literal _ -> ()
    | Char_literal _ -> ()
    | Apply(loc, f, args, tbinds) ->
        List.iter (fun (tp, ty) ->
            match ty with
                | Named_type({sym_kind=Type_param}, []) -> ()
                | _ -> (* TODO: Proper scope rules! *)
                    declare_vtable s ty) tbinds;
        declare_prereq_expr s f;
        List.iter (fun (param,arg) ->
            declare_prereq_expr s arg
        ) args
    | Record_cons(loc, _, fields) ->
        List.iter (fun (_, e) -> declare_prereq_expr s e) fields
    | Field_access(loc, e, _) -> declare_prereq_expr s e
    | Binop(loc, lhs, op, rhs) -> declare_prereq_expr s lhs; declare_prereq_expr s rhs
    | Deref(loc, ptr) -> declare_prereq_expr s ptr

and declare_vtable s ty =
    (*emit s ("extern const struct co_disp_ent " ^ c_name_of_vtable ty ^ "[];");
    emit s ""*)()

let declare_locals s proc_sym =
    List.iter (fun sym ->
        match sym.sym_kind with
            | Var ->
                emit s (c_name_of_type (unsome sym.sym_type)
                    ^ " " ^ c_name_of_var sym ^ ";");
            | _ -> ()
    ) proc_sym.sym_locals

let trans_sub s proc_sym =
    declare_prerequisites s proc_sym;
    proc_sym.sym_backend_translated <- 1;
    emit s (func_prototype s proc_sym);
    emit s "{";
    (let s = indent s in
        declare_locals s proc_sym;
        match proc_sym.sym_code with
            | Some stmts -> trans_istmts s stmts
            | None -> emit s "abort(); /* abstract procedure should never be called */"
    );
    emit s "}";
    emit s ""
