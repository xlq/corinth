open Big_int
open Symtab
open Misc

type state = {
    s_output: out_channel;
    s_scope: symbol;                (* scope that this state is for *)
    s_outer: state;                 (* state corresponding to next wider scope (widest scope points to self) *)
    s_scope_indent: int;            (* indent level of this scope *)
    mutable s_current_indent: int;  (* current indent level *)
    mutable s_lines: string list;   (* lines of Lua code (reverse order) *)
    s_temp_counter: int ref;
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
        s_temp_counter = s.s_temp_counter;
    } in
    let result = f new_state in (* if it fails, we discard the lines it produced *)
    let lines = new_state.s_lines in
    let lines = (*match lines with
        | _::_::_ -> ""::lines (* append blank line if more than one line *)
        | _ -> lines *) ""::lines
    in

    if appropriate_state.s_outer == appropriate_state then begin
        (* Safe to output. *)
        if lines <> [""] then
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
        s_temp_counter = ref 0;
    } in
    open_scope s root (fun s ->
        emit s "local function rv(x)";
        emit s "    if type(x) == \"table\" then";
        emit s "        local y = {}";
        emit s "        for k, v in pairs(x) do";
        emit s "            y[k] = v";
        emit s "        end";
        emit s "        return y";
        emit s "    else";
        emit s "        return x";
        emit s "    end";
        emit s "end";
        emit s "";
        emit s "local function printf(s, ...)";
        emit s "    print (string.format(s, ...))";
        emit s "end";
        emit s "";
    );
    s

let rec dotted_name_of_sym sym =
    if sym.sym_parent == sym then []
    else dotted_name_of_sym sym.sym_parent @ [sym.sym_name]

let lua_name_of_dotted_name parts =
    String.concat "__" (List.map String.lowercase parts)

let lua_name_of_local sym = String.lowercase sym.sym_name

let rec lua_name_of_sym sym =
    match sym with
        | {sym_kind=Proc; sym_imported=Some lua_name} -> lua_name
        | _ -> lua_name_of_dotted_name (dotted_name_of_sym sym)

and lua_name_of_var sym =
    match sym.sym_kind with
        | Proc -> lua_name_of_sym sym
        | Var ->
            begin match sym.sym_parent.sym_kind with
                | Proc -> lua_name_of_local sym (* local variable *)
                | Unit -> lua_name_of_sym sym   (* global variable *)
            end
        | Param -> lua_name_of_local sym

let lua_name_of_class_param i = "cls" ^ string_of_int i ^ "_"

let temp i = "tmp" ^ string_of_int i ^ "_"

let new_temp s =
    s.s_temp_counter := !(s.s_temp_counter) + 1;
    !(s.s_temp_counter)

let rec is_scalar = function
    | Boolean_type -> true
    | Char_type -> true
    | Integer_type -> true
    | Record_type _ -> false
    | Named_type({sym_kind=Type_sym; sym_type=Some t}, _) -> is_scalar t
    | Named_type({sym_kind=Type_param}, []) -> false
    | Pointer_type _ -> true
    | Proc_type _ -> true

let rec func_prototype s proc_sym =
    "function (" ^ String.concat ", "
        (List.map
         (fun (i, _) -> lua_name_of_class_param i)
         (enumerate proc_sym.sym_tconstraints)
         @ List.map lua_name_of_local (get_params proc_sym))
        ^ ")"

let rec return_list s proc_sym =
    List.map lua_name_of_local
        (List.filter (function
                      | {sym_kind=Param; sym_param_mode=Const_param} -> false
                      | {sym_kind=Param; sym_param_mode=Var_param|Out_param} -> true
                     ) (get_params proc_sym))

and trans_call s (returns: bool) iexpr =
    match iexpr with Apply(loc, proc_e, args, tbinds, classes) ->
    let replacements = ref [] in
    let translated = trans_iexpr s false proc_e ^ "("
        ^ String.concat ", "
            (List.map (function
                | Implement(cls, procs) ->
                    "{" ^ String.concat ", "
                        (List.map (fun (cls_proc, impl) ->
                            lua_name_of_local cls_proc ^ " = " ^ lua_name_of_sym impl
                            ) procs) ^ "}"
                | Forward i -> lua_name_of_class_param i
              ) !classes
               @ List.map (fun (param, arg) ->
                match param.sym_param_mode with
                    | Const_param -> trans_iexpr s true arg
                    | Var_param | Out_param ->
                        let arg' = trans_iexpr s true arg in
                        replacements := arg' :: !replacements;
                        arg'
                ) args)
        ^ ")"
    in
    if !replacements <> [] then begin
        if returns then begin
            let result = new_temp s in
            emit s ("local " ^ temp result);
            (* XXX: Incorrect: args might have side-effects so can't be repeated! *)
            emit s (String.concat ", " (List.rev !replacements) ^ ", " ^ temp result ^ " = " ^ translated);
            temp result
        end else begin
            emit s (String.concat ", " (List.rev !replacements) ^ " = " ^ translated ^ ";");
            ""
        end
    end else begin
        if returns then begin
            translated
        end else begin
            emit s translated;
            ""
        end
    end

and trans_iexpr s mut iexpr =
    let v x = if mut then x else "rv(" ^ x ^ ")" in
    match iexpr with
        | Name(loc, ({sym_kind=Param; sym_param_mode=Const_param} as sym)) ->
            (*assert (not mut);*)
            v (lua_name_of_var sym)
        | Name(loc, ({sym_kind=Param; sym_param_mode=(Var_param|Out_param)} as sym)) ->
            lua_name_of_var sym
        | Name(loc, {sym_kind=Const; sym_const=Some e}) ->
            trans_iexpr s mut e
        | Name(loc, {sym_kind=Const; sym_type=Some(Enum_type _); sym_name=name}) ->
            (* Enumeration elements are translated as strings. Easier to debug! *)
            "\"" ^ name ^ "\""
        | Name(loc, sym) ->
            trans s true sym;
            v (lua_name_of_var sym)
        | Int_literal(loc, n) ->
            string_of_big_int n
        | String_literal(loc, s) ->
            "\"" ^ s ^ "\""
        | Dispatch(index, cls_proc, tbinds) ->
            lua_name_of_class_param index ^ "." ^ lua_name_of_local cls_proc
        | Apply _ ->
            trans_call s true iexpr
        | Binop(loc, lhs, op, rhs) ->
            "(" ^ trans_iexpr s false lhs ^ ") "
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
                    | NE -> "~=")
                ^ " (" ^ trans_iexpr s false rhs ^ ")"
        | Record_cons(loc, rec_sym, fields) ->
            "{" ^ String.concat ", " (List.map (fun (field, value) ->
                lua_name_of_local field ^ " = " ^ trans_iexpr s false value
                ) fields) ^ "}"
        | Field_access(loc, lhs, field) ->
            "(" ^ (trans_iexpr s mut lhs) ^ ")." ^ lua_name_of_local field
        | New(loc, ty, e) ->
            "{rv(" ^ trans_iexpr s false e ^ ")}"
        | Deref(loc, ptr) ->
            trans_iexpr s false ptr ^ "[1]"
        | Genericify(e, _) -> trans_iexpr s mut e

and trans_istmt s = function
    | Call(loc, proc_e, args, tbinds, classes) ->
        ignore (trans_call s false (Apply(loc, proc_e, args, tbinds, classes)))
    | Assign(loc, dest, src) ->
        emit s (trans_iexpr s true dest ^ " = " ^ trans_iexpr s false src ^ ";")
    | Return(loc, None) ->
        emit s ("return " ^ String.concat ", " (return_list s s.s_scope))
    | Return(loc, Some e) ->
        emit s ("return " ^ String.concat ", " (return_list s s.s_scope @ [trans_iexpr s false e]))
    | If_stmt(if_parts, else_part) ->
        List.iter (fun (i, (loc, cond, body)) ->
            emit s ((if i == 0 then "if " else "elseif ") ^ trans_iexpr s false cond ^ " then");
            indent s (fun s -> trans_istmts s body)
        ) (enumerate if_parts);
        begin match else_part with
            | None -> ()
            | Some (loc, body) ->
                emit s "else";
                indent s (fun s -> trans_istmts s body)
        end;
        emit s "end"
    | While_stmt(loc, cond, body) ->
        emit s ("while " ^ trans_iexpr s false cond ^ " do");
        indent s (fun s -> trans_istmts s body);
        emit s "end"

and trans_istmts s = List.iter (trans_istmt s)

and trans s complete sym =
    match sym.sym_backend_translated, complete with
        | 0, true ->
            trans s false sym; (* pre-translate *)
            trans s true sym
        | 1, false | 2, _ -> ()
        | 0, false | 1, true ->
            sym.sym_backend_translated <- (if complete then 2 else 1);
            open_scope s sym (fun s ->
                match sym with
                    | {sym_kind=Type_sym} -> ()
                    | {sym_kind=Var} ->
                        if not complete then emit s ("local " ^ lua_name_of_var sym)
                    | {sym_kind=Proc; sym_imported=None} ->
                        if not complete then begin
                            emit s ("local " ^ lua_name_of_sym sym)
                        end else begin
                            emit s (lua_name_of_sym sym ^ " = " ^ func_prototype s sym);
                            indent s (fun s ->
                                trans_istmts s (unsome sym.sym_code);
                                let rec check_for_return = function
                                    | [] -> false
                                    | [Return _] -> true
                                    | _::rest -> check_for_return rest
                                in if not (check_for_return (unsome sym.sym_code)) then begin
                                    match return_list s sym with
                                        | [] -> ()
                                        | returns -> emit s ("return " ^ String.concat ", " returns)
                                end
                            );
                            emit s "end"
                        end
                    | {sym_kind=Proc; sym_imported=Some _} -> ()
                    | {sym_kind=Class} -> ()
            )

let translate s sym = trans s true sym
