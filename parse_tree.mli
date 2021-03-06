open Big_int

type loc = Lexing.position
type dotted_name = string list

type 'a args =
    'a list * (string * 'a) list

type unit_decl =
    | Unit of loc * dotted_name * decl list

and type_param = loc * string
and tconstraint = loc * dotted_name * ttype args

and decl =
    | Type_decl of loc * string * type_param list * type_defn
    | Var_decl of loc * string * ttype option * expr option
    | Proc_decl of loc * bool (* virtual? *) * string * type_param list * param list
        * ttype option (* return type *)
        * dotted_name option (* implements *)
        * proc_impl
    | Proc_import of loc * string * type_param list * param list * ttype option * dotted_name option * string
    | Const_decl of loc * string * expr

and proc_impl =
    | Body of stmt list
    | Abstract

and type_defn =
    | Type_alias of ttype
    | Record_type of (loc * string option * ttype) list

and param = loc * string * ttype option * Symtab.param_mode

and ttype =
    | Boolean_type
    | Integer_type (* for development *)
    | Char_type
    | Named_type of loc * dotted_name
    | Applied_type of loc * ttype * ttype args
    | Pointer_type of ttype
    | Proc_type of loc * type_param list * param list * ttype option
    | Enum_type of (loc * string) list

and stmt =
    | Decl of decl
    | Expr of expr
    | Assign of loc * expr * expr
    | Return of loc * expr option
    | If_stmt of (loc * expr * stmt list) list * (loc * stmt list) option
    | While_stmt of loc * expr * stmt list

and expr =
    | Name of loc * dotted_name
    | Int_literal of loc * big_int
    | String_literal of loc * string
    | Char_literal of loc * string
    | Apply of loc * expr * expr args
    | Record_cons of loc * expr args
    | Binop of loc * expr * Symtab.binop * expr
    | Deref of loc * expr
    | Not of loc * expr
    | New of loc * expr
    | Field_access of loc * expr * string
