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
    emit s "";
    s

let rec dotted_name_of_sym sym =
    if sym.sym_parent == sym then []
    else dotted_name_of_sym sym.sym_parent @ [sym.sym_name]

let c_name_of_dotted_name s parts =
    String.concat "__" (List.map String.lowercase parts)

let c_name_of_local s sym = String.lowercase sym.sym_name

let c_name_of_sym s sym =
    match sym with
        | {sym_kind=Proc; sym_imported=true} -> sym.sym_name
        | _ -> c_name_of_dotted_name s (dotted_name_of_sym sym)

let rec c_name_of_type_sym s sym =
    match sym with
        | {sym_kind=Type_sym; sym_type=Some (Record_type _)} ->
            "struct " ^ c_name_of_sym s sym
        | {sym_kind=Type_sym; sym_type=Some t} ->
            c_name_of_type s t

and c_name_of_type s = function
    | Boolean_type -> "bool"
    | Integer_type -> "int"
    | Char_type -> "char"
    | Named_type({sym_kind=Type_sym} as type_sym, _) -> c_name_of_type_sym s type_sym
    | Named_type({sym_kind=Type_param}, []) -> "void"
    | Pointer_type(t) -> c_name_of_type s t ^ "*"

let c_name_of_var s sym =
    match sym.sym_kind with
        | Proc -> c_name_of_sym s sym
        | Var ->
            begin match sym.sym_parent.sym_kind with
                | Proc -> c_name_of_local s sym (* local variable *)
                | Unit -> c_name_of_sym s sym   (* global variable *)
            end
        | Param -> c_name_of_local s sym

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

let rec trans_istmt s = function
    | Call(loc, proc_e, args) ->
        emit s (trans_iexpr s (Apply(loc, proc_e, args)) ^ ";")
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
            c_name_of_var s sym
        else
            "(*" ^ c_name_of_var s sym ^ ")"
    | Name(loc, {sym_kind=Const; sym_const=Some e}) ->
        trans_iexpr s e
    | Name(loc, sym) ->
        c_name_of_var s sym
    | Int_literal(loc, n) ->
        string_of_big_int n
    | String_literal(loc, s) ->
        "\"" ^ s ^ "\""
    | Char_literal(loc, s) ->
        "'" ^ String.make 1 s ^ "'"
    | Apply(loc, proc_e, args) ->
        trans_iexpr s proc_e ^ "("
        ^ String.concat ", " (List.map (fun (param, arg) ->
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
        "(" ^ c_name_of_type_sym s rec_sym ^ "){" ^
            String.concat ", " (List.map (fun (field, value) ->
                trans_iexpr s value) fields) ^ "}"
    | Field_access(loc, lhs, field) ->
        (trans_iexpr s lhs) ^ "." ^ c_name_of_local s field

let func_prototype s proc_sym =
    (match proc_sym.sym_type with
        | Some No_type -> "void"
        | Some t -> c_name_of_type s t)
    ^ " " ^ c_name_of_sym s proc_sym ^ "("
    ^ String.concat ", " (List.map (fun param ->
            c_name_of_type s (unsome param.sym_type)
            ^ " " ^ (if is_param_by_value param then "" else "*")
            ^ c_name_of_local s param
        ) (get_params proc_sym))
    ^ ")"

let rec declare s complete sym =
    if sym.sym_backend_translated < (if complete then 2 else 1) then begin
        if complete then declare_prerequisites s sym;
        match sym with
            | {sym_kind=Type_sym; sym_type=Some(Record_type None)} as type_sym ->
                if complete then begin
                    type_sym.sym_backend_translated <- 2;
                    emit s (c_name_of_type_sym s type_sym ^ " {");
                    begin let s = indent s in
                        List.iter (function
                            | {sym_kind=Type_param} -> ()
                            | {sym_kind=Var} as field ->
                                emit s (c_name_of_type s (unsome field.sym_type)
                                    ^ " " ^ c_name_of_local s field ^ ";")
                        ) type_sym.sym_locals
                    end;
                    emit s "};";
                    emit s ""
                end else begin
                    type_sym.sym_backend_translated <- 1;
                    emit s (c_name_of_type_sym s type_sym ^ ";") (* "struct foo;" *)
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
            List.iter (declare_prereq_stmt s) (unsome proc_sym.sym_code)

and declare_prereq_stmt s = function
    | Call(loc, f, args) ->
        declare_prereq_expr s (Apply(loc, f, args))
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
    | Apply(loc, f, args) ->
        declare_prereq_expr s f;
        List.iter (fun (param,arg) ->
            declare_prereq_expr s arg
        ) args
    | Record_cons(loc, _, fields) ->
        List.iter (fun (_, e) -> declare_prereq_expr s e) fields
    | Field_access(loc, e, _) -> declare_prereq_expr s e
    | Binop(loc, lhs, op, rhs) -> declare_prereq_expr s lhs; declare_prereq_expr s rhs

let declare_locals s proc_sym =
    List.iter (fun sym ->
        match sym.sym_kind with
            | Var ->
                emit s (c_name_of_type s (unsome sym.sym_type)
                    ^ " " ^ c_name_of_var s sym ^ ";");
            | _ -> ()
    ) proc_sym.sym_locals

let trans_sub s proc_sym =
    declare_prerequisites s proc_sym;
    emit s (func_prototype s proc_sym);
    emit s "{";
    (let s = indent s in
        declare_locals s proc_sym;
        trans_istmts s (unsome proc_sym.sym_code)
    );
    emit s "}";
    emit s ""
