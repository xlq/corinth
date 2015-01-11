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

and type_defn =
    | Type_alias of ttype
    | Record_type of (loc * string option * ttype) list

and param = loc * string * ttype option * bool

and ttype =
    | Integer_type (* for development *)
    | Named_type of loc * dotted_name
    | Applied_type of loc * ttype * ttype args
    | Pointer_type of ttype

and stmt =
    | Decl of decl
    | Expr of expr
    | Return of loc * expr option

and expr =
    | Name of loc * dotted_name
    | Int_literal of loc * big_int
    | Apply of loc * expr * expr args
    | Record_cons of loc * expr args
