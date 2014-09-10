%{
    type loc = Lexing.position

    open Parsing
    open Parse_tree
    open Errors

    let loc () = symbol_start_pos ()
    let string_of_dotted_name = String.concat "."
    let check_end (loc1, name1) (loc2, name2) =
        if name1 <> name2 then
            syntax_error loc2
                ("`end " ^ name2 ^ ";' should be `end "
                 ^ name1 ^ ";'.")
%}

%token <string> IDENT
%token <Big_int.big_int> INTEGER

/* Keywords */
%token CLASS END FUNCTION IS NULL OUT PROCEDURE RECORD TYPE UNIT VAR

%token LPAREN RPAREN LBRACKET RBRACKET COLON SEMICOLON DOT COMMA STAR
%token ASSIGN DOTDOT EQ NE LT GT LE GE ARROW PLUS DASH SLASH

%token EOF

%nonassoc EQ NE LT LE GT GE

%start unit_decl
%type <Parse_tree.unit_decl> unit_decl

%%

dotted_name:
    | IDENT { [$1] }
    | IDENT DOT dotted_name { $1 :: $3 }

ident_list:
    | IDENT { [$1] }
    | IDENT COMMA ident_list { $1::$3 }

unit_decl:
    | UNIT dotted_name SEMICOLON normal_decls
        { (loc(), $2, $4) }

normal_decls:
    | /* empty */ { [] }
    | decl normal_decls { $1::$2 }
    | var normal_decls { $1::$2 }

decl:
    | PROCEDURE IDENT opt_parameters IS compound_stmt END IDENT SEMICOLON
        { check_end (rhs_start_pos 2, $2) (rhs_start_pos 7, $7);
          Sub_decl(loc(), $2, $3, None, $5) }
    | FUNCTION IDENT opt_parameters COLON ttype IS compound_stmt END IDENT SEMICOLON
        { check_end (rhs_start_pos 2, $2) (rhs_start_pos 9, $9);
          Sub_decl(loc(), $2, $3, Some $5, $7) }
    | TYPE IDENT EQ type_defn SEMICOLON
        { let ending, defn = $4 in
          begin match ending with
            | Some ending -> check_end (rhs_start_pos 2, $2) ending
            | None -> ()
          end; Type_decl(loc(), $2, defn) }

var:
    | VAR ident_list COLON ttype SEMICOLON { Var_decl(loc(), $2, $4) }

field:
    | ident_list COLON ttype SEMICOLON { Var_decl(loc(), $1, $3) }

field_decls:
    | /* empty */ { [] }
    | decl field_decls { $1::$2 }
    | field field_decls { $1::$2 }

opt_parameters:
    | /* empty */ { [] }
    | LPAREN parameters RPAREN { $2 }

parameters:
    | parameter { [$1] }
    | parameter SEMICOLON parameters { $1::$3 }

parameter:
    | param_mode ident_list COLON ttype { (loc(), $1, $2, $4) }

param_mode:
    | /* empty */ { Const_param }
    | VAR         { Var_param }
    | OUT         { Out_param }

ttype:
    | dotted_name
        { if List.map String.lowercase $1 = ["integer"] then Integer else Named_type(loc(), $1) }

type_defn:
    | CLASS field_decls END IDENT
        { (Some (rhs_start_pos 4, $4),
           Class_defn(loc(), None, $2)) }
    | CLASS LPAREN dotted_name RPAREN field_decls END IDENT
        { (Some (rhs_start_pos 7, $7),
           Class_defn(rhs_start_pos 3, Some $3, $5)) }

compound_stmt:
    | NULL SEMICOLON { [] }
    | stmts { $1 }

stmts:
    | stmt { [$1] }
    | stmt stmts { $1::$2 }

stmt:
    | expr ASSIGN expr SEMICOLON { Assignment(loc(), $1, $3) }

expr:
    | dotted_name { Name(loc(), $1) }
    | expr PLUS expr { Binop(rhs_start_pos 2, $1, Add, $3) }
    | expr DASH expr { Binop(rhs_start_pos 2, $1, Subtract, $3) }
    | expr STAR expr { Binop(rhs_start_pos 2, $1, Multiply, $3) }
    | expr SLASH expr { Binop(rhs_start_pos 2, $1, Divide, $3) }
