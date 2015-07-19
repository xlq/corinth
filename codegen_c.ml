open Big_int
open Symtab
open Misc

type state = {
    s_output: out_channel;
    s_scope: symbol;                (* scope that this state is for *)
    s_outer: state;                 (* state corresponding to next wider scope (widest scope points to self) *)
    s_scope_indent: int;            (* indent level of this scope *)
    mutable s_current_indent: int;  (* current indent level *)
    mutable s_lines: string list;   (* lines of C code (reverse order) *)
}

let indent s f =
    s.s_current_indent <- s.s_current_indent + 1;
    let result = try f s
        with e -> s.s_current_indent <- s.s_current_indent - 1; raise e
    in
    s.s_current_indent <- s.s_current_indent - 1;
    result

let open_scope s scope f =
    let appropriate_state =
        let rec find_appropriate s =
            if s.s_scope == scope.sym_parent then s (* correct scope *)
            else if s.s_outer != s then find_appropriate s.s_outer (* try outer scope *)
            else s (* in another unit - use outermost (file) scope *)
        in find_appropriate s
    in
    (* Create new state for accumulating lines. *)
    let new_state = {
        s_output = s.s_output;
        s_scope = scope;
        s_outer = appropriate_state;
        s_scope_indent = appropriate_state.s_scope_indent + 1;
        s_current_indent = appropriate_state.s_scope_indent + 1; (* not an error - we start again at the indentation level of the parent scope *)
        s_lines = [];
    } in
    let result = f new_state in (* if it fails, we discard the lines it produced *)
    let lines = new_state.s_lines in
    let lines = (*match lines with
        | _::_::_ -> ""::lines (* append blank line if more than one line *)
        | _ -> lines *) ""::lines
    in

    if appropriate_state.s_outer == appropriate_state then begin
        (* Safe to output. *)
        List.iter (fun line ->
            output_string s.s_output (line ^ "\n")
        ) (List.rev lines)
    end else begin
        appropriate_state.s_lines <- (*appropriate_state.s_lines @ new_state.s_lines*)
            new_state.s_lines @ appropriate_state.s_lines
    end;
    result

let emit s line =
    s.s_lines <- (times s.s_current_indent "    " ^ line)::s.s_lines

let new_state root =
    let rec s = {
        s_output = stdout;
        s_scope = root;
        s_outer = s;
        s_scope_indent = -1;
        s_current_indent = 0;
        s_lines = [];
    } in
    open_scope s root (fun s ->
        emit s "#include <stdbool.h>";
        emit s "#include <stdlib.h>"
    );
    s

let rec dotted_name_of_sym sym =
    if sym.sym_parent == sym then []
    else dotted_name_of_sym sym.sym_parent @ [sym.sym_name]

let c_name_of_dotted_name parts =
    String.concat "__" (List.map String.lowercase parts)

let c_name_of_local sym = String.lowercase sym.sym_name

let rec c_name_of_sym sym =
    match sym with
        | {sym_kind=Proc; sym_imported=true} -> sym.sym_name
        | _ -> c_name_of_dotted_name (dotted_name_of_sym sym)

and c_name_of_type_sym sym =
    match sym with
        | {sym_kind=Type_sym; sym_type=Some (Record_type _)} ->
            "struct " ^ c_name_of_sym sym

and c_name_of_var sym =
    match sym.sym_kind with
        | Proc -> c_name_of_sym sym
        | Var ->
            begin match sym.sym_parent.sym_kind with
                | Proc -> c_name_of_local sym (* local variable *)
                | Unit -> c_name_of_sym sym   (* global variable *)
            end
        | Param -> c_name_of_local sym

and class_vtable_type s cls = "struct " ^ c_name_of_sym cls ^ "__VTABLE"

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

let rec func_prototype s complete proc_sym =
    (match proc_sym.sym_type with
        | Some No_type -> "void"
        | Some t -> trans_type s complete t)
    ^ " " ^ c_name_of_sym proc_sym ^ "("
    ^ String.concat ", "
        (List.map (fun (i, (cls, _)) ->
            trans s true cls;
            class_vtable_type s cls ^ " *cls" ^ string_of_int i ^ "_"
         ) (enumerate proc_sym.sym_tconstraints)
         @ List.map (fun param ->
            trans_type s complete (unsome param.sym_type)
            ^ " " ^ (if is_param_by_value param then "" else "*")
            ^ c_name_of_local param
         ) (get_params proc_sym))
    ^ ")"

(* Return the function pointer type for this class procedure. *)
(* XXX: This is very similar to the above. *)
and class_func_ptr_type s proc_sym inner =
    (match proc_sym.sym_type with
        | Some No_type -> "void"
        | Some t -> trans_type s false t)
    ^ " (*" ^ (if inner <> "" then " " ^ inner else "") ^ ")(" ^ String.concat ", "
        (List.map (fun (cls, _) -> class_vtable_type s cls) proc_sym.sym_tconstraints
         @ List.map (fun param ->
            trans_type s false (unsome param.sym_type)
            ^ (if is_param_by_value param then "" else "*")) (get_params proc_sym))
    ^ ")"

and trans_istmt s = function
    | Call(loc, proc_e, args, tbinds, classes) ->
        emit s (trans_iexpr s false (Apply(loc, proc_e, args, tbinds, classes)) ^ ";")
    | Assign(loc, dest, src) ->
        emit s (trans_iexpr s false dest ^ " = " ^ trans_iexpr s false src ^ ";")
    | Return(loc, None) ->
        emit s ("return;")
    | Return(loc, Some e) ->
        emit s ("return " ^ trans_iexpr s false e ^ ";")
    | If_stmt(if_parts, else_part) ->
        List.iter (fun (loc, cond, body) ->
            emit s ("if (" ^ trans_iexpr s false cond ^ "){");
            indent s (fun s -> trans_istmts s body)
        ) if_parts;
        begin match else_part with
            | None -> ()
            | Some (loc, body) ->
                emit s ("} else {");
                indent s (fun s -> trans_istmts s body)
        end;
        emit s "}"
    | While_stmt(loc, cond, body) ->
        emit s ("while (" ^ trans_iexpr s false cond ^ "){");
        indent s (fun s -> trans_istmts s body);
        emit s "}"

and trans_istmts s = List.iter (trans_istmt s)

and trans_iexpr s pointer_wanted iexpr =
    let v result =
        if pointer_wanted then "&" ^ result else result
    and p result =
        if pointer_wanted then result else "*" ^ result
    in match iexpr with
        | Name(loc, ({sym_kind=Param} as sym)) ->
            if is_param_by_value sym then
                v (c_name_of_var sym)
            else
                p (c_name_of_var sym)
        | Name(loc, {sym_kind=Const; sym_const=Some e}) ->
            trans_iexpr s pointer_wanted e
        | Name(loc, sym) ->
            trans s true sym;
            v (c_name_of_var sym)
        | Int_literal(loc, n) ->
            string_of_big_int n
        | String_literal(loc, s) ->
            "\"" ^ s ^ "\""
        | Char_literal(loc, s) ->
            "'" ^ s ^ "'"
        | Dispatch(index, cls_proc, tbinds) ->
            "cls" ^ string_of_int index ^ "_->"
                ^ c_name_of_local cls_proc
        | Apply(loc, proc_e, args, tbinds, classes) ->
            v (trans_iexpr s false proc_e ^ "("
            ^ String.concat ", "
                (List.map (fun (cls, procs) ->
                    "&(" ^ class_vtable_type s cls ^ "){"
                    ^ String.concat ", "
                        (List.map (fun (cls_proc, impl) ->
                            "(" ^ class_func_ptr_type s cls_proc ""
                                ^ ") " ^ c_name_of_sym impl) procs)
                    ^ "}") !classes
                 @ List.map (fun (param, arg) ->
                    trans_iexpr s (not (is_param_by_value param)) arg) args) ^ ")")
        | Binop(loc, lhs, op, rhs) ->
            v ("(" ^ trans_iexpr s false lhs ^ ") "
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
                ^ " (" ^ trans_iexpr s false rhs ^ ")")
        | Record_cons(loc, rec_sym, fields) ->
            v ("(" ^ c_name_of_type_sym rec_sym ^ "){" ^
                String.concat ", " (List.map (fun (field, value) ->
                    trans_iexpr s false value) fields) ^ "}")
        | Field_access(loc, lhs, field) ->
            v ("(" ^ (trans_iexpr s false lhs) ^ ")." ^ c_name_of_local field)
        | Deref(loc, ptr) ->
            "*(" ^ trans_iexpr s false ptr ^ ")"
        | New(loc, ty) ->
            "malloc(sizeof(" ^ trans_type s true ty ^ "))"

and trans s complete sym =
    (* Already translated? *)
    let desired_trans_level = if complete then 2 else 1 in
    if sym.sym_backend_translated < desired_trans_level then begin
        (* Need to translate. *)
        sym.sym_backend_translated <- desired_trans_level;
        open_scope s sym (fun s ->
            match sym with
                | {sym_kind=Type_sym; sym_type=Some(Record_type None)} ->
                    (* Record type. *)
                    if not complete then begin
                        emit s (c_name_of_type_sym sym ^ ";") (* "struct foo;" *)
                    end else begin
                        emit s (c_name_of_type_sym sym ^ " {");
                        indent s (fun s ->
                            List.iter (function
                                | {sym_kind=Type_param} -> ()
                                | {sym_kind=Var} as field ->
                                    emit s (trans_type s true (unsome field.sym_type)
                                        ^ " " ^ c_name_of_local field ^ ";")
                            ) sym.sym_locals
                        );
                        emit s "};"
                    end
                | {sym_kind=Type_sym; sym_type=Some ty} ->
                    (* Type aliases aren't translated into C - translator
                       just uses the original type, so make sure that's declared. *)
                    ignore (trans_type s complete ty)
                | {sym_kind=Var} ->
                    emit s (trans_type s true (unsome sym.sym_type) ^ " " ^ c_name_of_var sym ^ ";")
                | {sym_kind=Proc} ->
                    if not complete then begin
                        emit s (func_prototype s false sym ^ ";")
                    end else begin
                        emit s (func_prototype s true sym);
                        emit s "{";
                        indent s (fun s ->
                            trans_istmts s (unsome sym.sym_code)
                        );
                        emit s "}"
                    end
                | {sym_kind=Class} ->
                    (* Declare the class vtable struct. *)
                    emit s (class_vtable_type s sym ^ " {");
                    indent s (fun s ->
                        List.iter (fun cls_proc ->
                            emit s (class_func_ptr_type s cls_proc (c_name_of_local cls_proc) ^ ";")
                        ) (List.filter (is_kind Class_proc) sym.sym_locals)
                    );
                    emit s "};"
        )
    end

and trans_type s complete = function
    | Boolean_type -> "bool"
    | Integer_type -> "int"
    | Char_type -> "char"
    | Named_type({sym_kind=Type_sym; sym_type=Some(Record_type _)} as type_sym, _) ->
        trans s complete type_sym;
        c_name_of_type_sym type_sym
    | Named_type({sym_kind=Type_sym; sym_type=Some ty}, _) ->
        trans_type s complete ty
    | Named_type({sym_kind=Type_param}, []) -> "void"
    | Pointer_type(t) -> trans_type s false t ^ " *"

let translate s sym = trans s true sym
