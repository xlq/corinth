%{
    type loc = Lexing.position

    open Parsing
    open Parse_tree
    open Errors
    open Misc

    let loc () = symbol_start_pos ()
    let string_of_dotted_name = String.concat "."
    let check_end (loc1, name1) (loc2, name2) =
        if name1 <> name2 then
            syntax_error loc2
                ("`end " ^ name2 ^ ";' should be `end "
                 ^ name1 ^ ";'.")
%}

%token <string> IDENT
%token <string> STRING
%token <Big_int.big_int> INTEGER
%token <string> CHARLIT

/* Keywords */
%token ABSTRACT AND CONST ELSE ELSIF END IF IMPLEMENTS IMPORTED IS LOOP NEW NOT OR OUT
%token OVERRIDING PROC RETURN THEN TYPE UNIT VAR VIRTUAL WHILE WITH

%token LPAREN RPAREN LBRACE RBRACE QUESTION COLON SEMICOLON DOT COMMA STAR
%token ASSIGN DOTDOT EQ NE LT GT LE GE ARROW PLUS DASH SLASH CARET MID

%token EOF

%start unit_decl
%type <Parse_tree.unit_decl> unit_decl

%left OR
%left AND
%right NOT
%left LT GT LE GE EQ NE
%left PLUS DASH
%left STAR SLASH
%left LPAREN
%left NEW
%right CARET
%left DOT

%%

dotted_name:
    | IDENT { [$1] }
    | IDENT DOT dotted_name { $1 :: $3 }

ident_list:
    | IDENT { [loc(), $1] }
    | IDENT COMMA ident_list { (loc(), $1)::$3 }

ttype_inner:
    | dotted_name {
        match $1 with
            | ["bool"] -> Boolean_type
            | ["int"] -> Integer_type
            | ["char"] -> Char_type
            | _ -> Named_type(loc(), $1)
        }
    | ttype_inner LT type_args GT { Applied_type(loc(), $1, $3) }
    | PROC opt_type_params LPAREN params RPAREN opt_type
        { Proc_type(loc(), $2, $4, $6) }
    | LPAREN ident_list RPAREN
        { Enum_type($2) }

ttype:
    | ttype_inner { $1 }
    | CARET ttype { Pointer_type($2) }

type_args:
    | ttype { ([$1], []) }
    | ttype COMMA type_args { let a,b = $3 in ($1::a,b) }
    | type_assocs { ([], $1) }
type_assocs:
    | type_assoc { [$1] }
    | type_assoc COMMA type_assocs { $1::$3 }
type_assoc:
    | IDENT ARROW ttype { ($1, $3) }

type_defn:
    | ttype { Type_alias($1) }
    | record_type { Record_type($1) }
record_type:
    | LBRACE record_fields RBRACE { $2 }
record_fields:
    | /* empty */ { [] }
    | record_field { [$1] }
    | record_field COMMA record_fields { $1::$3 }
record_field:
    | IDENT COLON ttype { (loc(), Some $1, $3) }
    | ttype { (loc(), None, $1) }

decls:
    | /* empty */ { [] }
    | decl decls { $1::$2 }
decl:
    | TYPE IDENT opt_type_params EQ type_defn SEMICOLON
        { Type_decl(loc(), $2, $3, $5) }
    | VAR IDENT opt_type opt_init SEMICOLON
        { Var_decl(loc(), $2, $3, $4) }
    | opt_virtual PROC IDENT opt_type_params LPAREN params RPAREN opt_type opt_implements IS proc_body END IDENT SEMICOLON
        { check_end (rhs_start_pos 3, $3) (rhs_start_pos 13, $13);
          Proc_decl(loc(), $1, $3, $4, $6, $8, $9, Body $11) }
    | opt_virtual PROC IDENT opt_type_params LPAREN params RPAREN opt_type opt_implements IS ABSTRACT SEMICOLON
        { if not $1 then syntax_error (loc()) "Only virtual procedures can be abstract.";
          Proc_decl(loc(), true, $3, $4, $6, $8, $9, Abstract) }
    | opt_virtual PROC IDENT opt_type_params LPAREN params RPAREN opt_type opt_implements IS IMPORTED STRING SEMICOLON
        { if $1 then syntax_error (loc()) "Imported procedure cannot be virtual.";
          Proc_import(loc(), $3, $4, $6, $8, $9, $12) }
    | CONST IDENT ASSIGN expr SEMICOLON
        { Const_decl(loc(), $2, $4) }

opt_virtual:
    | /* empty */ { false }
    | VIRTUAL { true }
opt_type_params:
    | /* empty */ { [] }
    | LT type_params GT { $2 }
type_params:
    | /* empty */ { [] }
    | type_param { [$1] }
    | type_param COMMA type_params { $1::$3 }
type_param:
    | IDENT { (loc(), $1) }
opt_implements:
    | /* empty */ { None }
    | IMPLEMENTS dotted_name { Some $2 }

opt_init:
    | /* empty */ { None }
    | ASSIGN expr { Some $2 }

params:
    | /* empty */ { [] }
    | param { [$1] }
    | param COMMA params { $1::$3 }
param:
    | opt_mode IDENT opt_type { (loc(), $2, $3, $1) }
opt_mode:
    | /* empty */ { Symtab.Const_param }
    | VAR { Symtab.Var_param }
    | OUT { Symtab.Out_param }
opt_type:
    | /* empty */ { None }
    | COLON ttype { Some $2 }

proc_body:
    | /* empty */ { [] }
    | decl_or_stmt proc_body { $1::$2 }

decl_or_stmt:
    | decl { Decl $1 }
    | stmt { $1 }
stmt:
    | expr SEMICOLON { Expr $1 }
    | expr ASSIGN expr SEMICOLON { Assign(loc(), $1, $3) }
    | RETURN expr SEMICOLON { Return(loc(), Some $2) }
    | RETURN SEMICOLON { Return(loc(), None) }
    | IF expr THEN proc_body else_parts END IF SEMICOLON {
        let elsif_parts, else_part = $5 in
        If_stmt((loc(), $2, $4) :: elsif_parts, else_part) }
    | WHILE expr LOOP proc_body END LOOP SEMICOLON
        { While_stmt(loc(), $2, $4) }

else_parts:
    | /* empty */ { ([], None) }
    | ELSIF expr THEN proc_body else_parts
        { let a, b = $5 in ((loc(), $2, $4) :: a, b) }
    | ELSE proc_body
        { ([], Some(loc(), $2)) }

expr:
    | LPAREN expr RPAREN { $2 }
    | dotted_name { Name(loc(), $1) }
    | INTEGER { Int_literal(loc(), $1) }
    | STRING { String_literal(loc(), $1) }
    | CHARLIT { Char_literal(loc(), $1) }
    | expr LPAREN expr_map RPAREN { Apply(loc(), $1, $3) }
    | expr LPAREN RPAREN { Apply(loc(), $1, ([], [])) }
    | LBRACE expr_map RBRACE { Record_cons(loc(), $2) }
    | expr PLUS expr { Binop(rhs_start_pos 2, $1, Symtab.Add, $3) }
    | expr DASH expr { Binop(loc(), $1, Symtab.Subtract, $3) }
    | expr STAR expr { Binop(loc(), $1, Symtab.Multiply, $3) }
    | expr SLASH expr { Binop(loc(), $1, Symtab.Divide, $3) }
    | expr LT expr { Binop(loc(), $1, Symtab.LT, $3) }
    | expr GT expr { Binop(loc(), $1, Symtab.GT, $3) }
    | expr LE expr { Binop(loc(), $1, Symtab.LE, $3) }
    | expr GE expr { Binop(loc(), $1, Symtab.GE, $3) }
    | expr EQ expr { Binop(loc(), $1, Symtab.EQ, $3) }
    | expr NE expr { Binop(loc(), $1, Symtab.NE, $3) }
    | expr AND expr { Binop(loc(), $1, Symtab.And, $3) }
    | expr OR expr { Binop(loc(), $1, Symtab.Or, $3) }
    | expr CARET { Deref(loc(), $1) }
    | NOT expr { Not(loc(), $2) }
    | NEW expr { New(loc(), $2) }
    | expr DOT IDENT { Field_access(rhs_start_pos 3, $1, $3) }

expr_map:
    | expr { ([$1], []) }
    | expr COMMA expr_map { let a,b = $3 in ($1::a,b) }
    | expr_assocs { ([], $1) }
expr_assocs:
    | expr_assoc { [$1] }
    | expr_assoc COMMA expr_assocs { $1::$3 }
expr_assoc:
    | IDENT ARROW expr { ($1, $3) }

unit_decl:
    | UNIT dotted_name SEMICOLON decls { Unit(loc(), $2, $4) }
