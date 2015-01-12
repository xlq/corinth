open Big_int

type loc = Lexing.position
type dotted_name = string list

type 'a args =
    'a list * (string * 'a) list

type unit_decl =
    | Unit of loc * dotted_name * decl list

and decl =
    | Type_decl of loc * string * (loc * string) list * type_defn
    | Var_decl of loc * string * ttype option * expr option
    | Proc_decl of loc * string * (loc * string) list * param list * ttype option * stmt list
    | Proc_import of loc * string * (loc * string) list * param list * ttype option
    | Const_decl of loc * string * expr

and type_defn =
    | Type_alias of ttype
    | Record_type of (loc * string option * ttype) list

and param = loc * string * ttype option * Symtab.param_mode * bool

and ttype =
    | Boolean_type
    | Integer_type (* for development *)
    | Char_type
    | Named_type of loc * dotted_name
    | Applied_type of loc * ttype * ttype args
    | Pointer_type of ttype

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
