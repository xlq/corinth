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

let c_name_of_type s = function
    | Integer_type -> "int"

let rec c_unit_prefix s unit =
    if unit.sym_parent == unit then ""
    else c_unit_prefix s unit.sym_parent ^ String.lowercase unit.sym_name ^ "__"

let c_name_of_sub s sub =
    c_unit_prefix s sub.sym_parent ^ String.lowercase sub.sym_name

let c_name_of_param s param = String.lowercase param.sym_name

let c_name_of_var s sym =
    match sym.sym_kind with
        | Parameter -> c_name_of_param s sym
        | Variable -> c_unit_prefix s sym.sym_parent ^ String.lowercase sym.sym_name

let rec trans_istmt s = function
    | Assignment(loc, lhs, rhs) ->
        emit s ("(" ^ trans_iexpr s lhs ^ ") = (" ^ trans_iexpr s rhs ^ ");")

and trans_istmts s = List.iter (trans_istmt s)

and trans_iexpr s = function
    | Name(loc, sym) ->
        c_name_of_var s sym
    | Binop(loc, lhs, op, rhs) ->
        "(" ^ trans_iexpr s lhs ^ ") "
            ^ (match op with
                | Add -> "+"
                | Subtract -> "-"
                | Multiply -> "*"
                | Divide -> "/")
            ^ " (" ^ trans_iexpr s rhs ^ ")"

let trans_sub s sub_sym =
    emit s ((match sub_sym.sym_type with
            | None -> "void"
            | Some t -> c_name_of_type s t)
        ^ " " ^ c_name_of_sub s sub_sym ^ "("
        ^ String.concat ", " (List.map (fun param ->
                c_name_of_type s (unsome param.sym_type)
                ^ " " ^ c_name_of_param s param
            ) (parameters sub_sym))
        ^ ")\n");
    trans_istmts (indent s) (unsome sub_sym.sym_code);
    emit s "}"
