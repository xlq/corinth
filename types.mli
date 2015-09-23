open Symtab

type context

(* All the situations in which a type mismatch might arise. *)
type situation =
    | SVar_init of symbol        (* variable initialisation *)
    | SCall_none        (* call statement must have no return type *)
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

(* All the reasons for a type mismatch. *)
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

val new_context : unit -> context
val coerce : context -> situation list -> ttype -> ttype -> unit
