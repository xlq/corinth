open Symtab
open Types
open Misc

exception Internal_error
exception Compile_error

let string_of_location loc =
    loc.Lexing.pos_fname ^ ":"
    ^ string_of_int loc.Lexing.pos_lnum ^ ":"
    ^ string_of_int (loc.Lexing.pos_cnum + 1 - loc.Lexing.pos_bol)

let syntax_error loc s =
    prerr_endline (string_of_location loc ^ ": " ^ s)

let semantic_error = syntax_error

let internal_error loc s =
    syntax_error loc ("Internal error: " ^ s);
    raise Internal_error

let rec describe_situations sits =
    let continue = function
        | [] -> ""
        | (_::_) as tail -> "," ^ describe_situations tail
    in match sits with
    | SReturn_type::SApply(Some p)::tail ->
        " for return type of procedure `" ^ p.sym_name ^ "'" ^ continue tail
    | SReturn_type::SApply(None)::tail ->
        " for return type of procedure" ^ continue tail
    | situation::tail ->
        " " ^ begin match situation with
            | SVar_init s -> "when initialising " ^ describe_sym s ^ " `" ^ s.sym_name ^ "'"
            | SAssign -> "for this assignment"
            | SReturn_stat -> "in this return statement"
            | SCondition -> "in this condition"
            | SApply(Some p) -> "when calling procedure `" ^ p.sym_name ^ "'"
            | SApply(None) -> "when calling procedure"
            | SParameter param -> "for parameter `" ^ unsome param.param_name ^ "'"
            | SRecord_cons -> "in record constructor"
            | SBoolean_op -> "for Boolean operation"
            | SBinop -> "for operator"
            | SField field -> "for field `" ^ field.field_name ^ "'"
        end ^ continue tail

(* Is this situation in a procedure call? *)
let is_call = function
    | SApply _ :: _
    | SParameter _ :: SApply _ :: _ -> true
    | _ -> false

let one_of s a b default =
    match a, b with
        | Some a, _ -> s ^ " `" ^ a ^ "'"
        | None, Some b -> s ^ " `" ^ b ^ "'"
        | None, None -> default

let type_error loc (situations, err) =
    match situations, err with
        | SReturn_type::SApply(Some p)::tail, ESimply_wrong(TNone, t2) ->
            semantic_error loc ("Procedure `" ^ p.sym_name ^ "' doesn't return a value.")
        | SReturn_type::SApply(None)::tail, ESimply_wrong(TNone, t2) ->
            semantic_error loc ("This procedure doesn't return a value.")
    | _ -> match err with
        | EField_count(rec1, rec2) ->
            semantic_error rec1.rec_loc ("This record has too "
                ^ (if List.length rec1.rec_fields > List.length rec2.rec_fields
                   then "many" else "few") ^ " fields" ^ describe_situations situations ^ ".")
        | EField_order(field1, field2) ->
            semantic_error field1.field_loc ("This field is named `" ^ field1.field_name ^ "'" ^ describe_situations situations);
            semantic_error field2.field_loc ("...but should be named `" ^ field2.field_name ^ "'.")
        | EParam_mode(param1, param2) ->
            if is_call situations then begin
                semantic_error param2.param_loc
                    ("Cannot assign to this expression. "
                     ^ one_of "Parameter" param1.param_name param2.param_name "This parameter"
                     ^ " is declared " ^ param_mode_name param1.param_mode ^ ".")
            end else begin
                semantic_error param1.param_loc
                    ((match param1.param_name with
                        | Some s -> "Parameter `" ^ s ^ "'"
                        | None -> "This parameter")
                    ^ " is " ^ param_mode_name param1.param_mode);
                semantic_error param2.param_loc
                    ("...but should be " ^ param_mode_name param2.param_mode
                     ^ describe_situations situations)
            end
        | EParam_count(proc1, proc2) ->
            let many = List.length proc1.proc_params > List.length proc2.proc_params in
            if is_call situations then begin
                semantic_error proc2.proc_loc
                    (if many then "Not enough arguments." else "Too many arguments.")
            end else begin
                semantic_error proc1.proc_loc ("This proc has too "
                    ^ (if many then "many" else "few") ^ " parameters" ^ describe_situations situations)
            end
        | EParam_missing_left(param) ->
            if is_call situations then begin
                semantic_error param.param_loc
                    ("There is no such parameter `" ^ unsome param.param_name ^ "'"
                        ^ describe_situations situations)
            end else begin
                semantic_error param.param_loc
                    ((match param.param_name with Some s -> "Parameter `" ^ s ^ "'"
                                                | None -> "This parameter")
                        ^ " is not provided" ^ describe_situations situations)
            end
        | ESimply_wrong(t1, t2) ->
            semantic_error loc ("Expected type `" ^ string_of_type t2
                ^ "' but got `" ^ string_of_type t1 ^ "'"
                ^ describe_situations situations)
