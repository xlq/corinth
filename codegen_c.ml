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
    c_name_of_dotted_name s (dotted_name_of_sym sym)

let c_name_of_type_sym s sym =
    match sym with
        | {sym_kind=Type_sym; sym_type=Some (Record_type _)} ->
            "struct " ^ c_name_of_sym s sym

let c_name_of_type s = function
    | Boolean_type -> "bool"
    | Integer_type -> "int"
    | Named_type({sym_kind=Type_sym} as type_sym, _) -> c_name_of_type_sym s type_sym
    | Named_type({sym_kind=Type_param}, []) -> "void"

let c_name_of_var s sym =
    match sym.sym_kind with
        | Proc -> c_name_of_sym s sym
        | Var ->
            begin match sym.sym_parent.sym_kind with
                | Proc -> c_name_of_local s sym (* local variable *)
                | Unit -> c_name_of_sym s sym   (* global variable *)
            end
        | Param -> c_name_of_local s sym
        | Temp -> "t" ^ sym.sym_name ^ "_"

let rec is_scalar = function
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

and trans_istmts s = List.iter (trans_istmt s)

and trans_iexpr s = function
    | Name(loc, ({sym_kind=Param} as sym)) ->
        if is_param_by_value sym then
            c_name_of_var s sym
        else
            "(*" ^ c_name_of_var s sym ^ ")"
    | Name(loc, sym) ->
        c_name_of_var s sym
    | Int_literal(loc, n) ->
        string_of_big_int n
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
    if not sym.sym_backend_translated then begin
        if complete then declare_prerequisites s sym;
        match sym with
            | {sym_kind=Type_sym; sym_type=Some(Record_type None)} as type_sym ->
                if complete then begin
                    type_sym.sym_backend_translated <- true;
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
                    emit s (c_name_of_type_sym s type_sym ^ ";") (* "struct foo;" *)
                end
            | {sym_kind=Proc} as proc_sym ->
                emit s (func_prototype s proc_sym ^ ";")
    end

and declare_type s complete = function
    | No_type -> ()
    | Pointer_type(t) ->
        declare_type s false t
    | Boolean_type -> ()
    | Integer_type -> ()
    | Named_type({sym_kind=Type_param}, []) -> ()
    | Named_type({sym_kind=Type_sym} as type_sym, _) -> declare s complete type_sym

and declare_prerequisites s = function
    | {sym_kind=Type_sym; sym_type=Some(Record_type None)} as type_sym ->
        List.iter (function
            | {sym_kind=Type_param} -> ()
            | {sym_kind=Var} as field ->
                declare_type s true (unsome field.sym_type)
        ) type_sym.sym_locals
    | {sym_kind=Var|Param|Temp} as var_sym ->
        declare_type s true (unsome var_sym.sym_type)
    | {sym_kind=Type_param} -> ()
    | {sym_kind=Proc} as proc_sym ->
        declare_type s true (unsome proc_sym.sym_type);
        List.iter (declare_prerequisites s) proc_sym.sym_locals

let declare_locals s proc_sym =
    List.iter (fun sym ->
        match sym.sym_kind with
            | Var|Temp ->
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
