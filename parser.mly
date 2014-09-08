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
%token END FUNCTION IS OUT PROCEDURE RECORD TYPE UNIT VAR

%token LPAREN RPAREN LBRACKET RBRACKET COLON SEMICOLON DOT COMMA STAR
%token ASSIGN DOTDOT EQ NE LT GT LE GE ARROW

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
    | UNIT dotted_name SEMICOLON decls
        { (loc(), $2, $4) }

decls:
    | /* empty */ { [] }
    | decl decls { $1::$2 }

decl:
    | ident_list COLON ttype SEMICOLON { Var_decl(loc(), $1, $3) }
    | PROCEDURE IDENT opt_parameters SEMICOLON { Sub_decl(loc(), $2, $3, None) }
    | FUNCTION IDENT opt_parameters COLON ttype SEMICOLON { Sub_decl(loc(), $2, $3, Some $5) }

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
        { if List.map String.lowercase $1 = ["integer"] then Integer else Named_type $1 }
