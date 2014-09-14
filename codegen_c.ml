open Symtab
open Misc

type state = {
    s_output: out_channel;
    s_indent: int;
}

let new_state () =
    {
        s_output = stdout;
        s_indent = 0;
    }

let emit s line = output_string s.s_output (times s.s_indent "    " ^ line ^ "\n")

let indent s = {s with s_indent = s.s_indent + 1}

let rec dotted_name_of_sym sym =
    if sym.sym_parent == sym then []
    else dotted_name_of_sym sym.sym_parent @ [sym.sym_name]

let c_name_of_dotted_name s parts =
    String.concat "__" (List.map String.lowercase parts)

let c_name_of_local s sym = String.lowercase sym.sym_name

let c_name_of_sym s sym =
    c_name_of_dotted_name s (dotted_name_of_sym sym)

let c_name_of_type_sym s sym =
    match sym.sym_kind with
        | Unit | Variable | Subprogram | Parameter -> assert false
        | Class_type -> "struct " ^ c_name_of_sym s sym

let c_name_of_type s = function
    | Integer_type -> "int"
    | Named_type(tp) -> c_name_of_type_sym s tp

let c_name_of_var s sym =
    match sym.sym_kind with
        | Unit | Subprogram | Class_type -> assert false
        | Parameter -> c_name_of_local s sym
        | Variable -> c_name_of_sym s sym

let rec trans_istmt s = function
    | Assignment(loc, lhs, rhs) ->
        emit s ("(" ^ trans_iexpr s lhs ^ ") = (" ^ trans_iexpr s rhs ^ ");")

and trans_istmts s = List.iter (trans_istmt s)

and trans_iexpr s = function
    | Name(loc, sym) -> begin
        match sym.sym_kind, sym.sym_param_mode with
            | Parameter, (Var_param|Out_param) ->
                "(*" ^ c_name_of_var s sym ^ ")"
            | _ -> c_name_of_var s sym
    end
    | Binop(loc, lhs, op, rhs) ->
        "(" ^ trans_iexpr s lhs ^ ") "
            ^ (match op with
                | Add -> "+"
                | Subtract -> "-"
                | Multiply -> "*"
                | Divide -> "/")
            ^ " (" ^ trans_iexpr s rhs ^ ")"

let is_scalar = function
    | Integer_type -> true
    | Named_type(type_sym) ->
        match type_sym.sym_kind with
            | Unit | Variable | Subprogram | Parameter -> assert false
            | Class_type -> false

let is_param_by_value param_sym =
    match param_sym.sym_param_mode with
        | Var_param | Out_param -> false
        | Const_param -> is_scalar (unsome param_sym.sym_type)

let func_prototype s sub_sym =
    (match sub_sym.sym_type with
        | None -> "void"
        | Some t -> c_name_of_type s t)
    ^ " " ^ c_name_of_sym s sub_sym ^ "("
    ^ String.concat ", " (List.map (fun param ->
            c_name_of_type s (unsome param.sym_type)
            ^ " " ^ (if is_param_by_value param then "" else "*")
            ^ c_name_of_local s param
        ) (parameters sub_sym))
    ^ ")"

let trans_sub s sub_sym =
    let prerequisites = find_needed_syms sub_sym in
    List.iter (fun sym ->
        if not sym.sym_translated then begin
            sym.sym_translated <- true;
            match sym.sym_kind with
                | Unit -> assert false;
                | Variable ->
                    if sym.sym_parent.sym_kind = Unit then begin
                        if sym.sym_parent == sub_sym then () else
                            emit s ("extern " ^ c_name_of_type s (unsome sym.sym_type)
                                ^ " " ^ c_name_of_var s sym ^ ";")
                    end
                | Parameter ->
                    assert (sym.sym_parent == sub_sym)
                | Class_type ->
                    emit s (c_name_of_type_sym s sym ^ " {");
                    begin let s = indent s in
                        List.iter (fun member ->
                            match member.sym_kind with
                                | Unit | Parameter | Class_type -> assert false
                                | Variable ->
                                    emit s (c_name_of_type s (unsome member.sym_type)
                                        ^ " " ^ c_name_of_local s member ^ ";")
                                | Subprogram -> ()
                        ) sym.sym_locals
                    end;
                    emit s "};";
                    emit s ""
                | Subprogram ->
                    emit s (func_prototype s sym ^ ";")
        end
    ) prerequisites;

    emit s "";

    emit s (func_prototype s sub_sym);
    emit s "{";
    trans_istmts (indent s) (unsome sub_sym.sym_code);
    emit s "}"
