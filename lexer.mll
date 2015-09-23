{
    open Parser
    open Big_int

    let create_hashtable init =
        let tbl = Hashtbl.create (List.length init) in
        List.iter (fun (key,data) -> Hashtbl.add tbl key data) init;
        tbl

    let keywords = create_hashtable [
        "abstract",      ABSTRACT;
        "and",           AND;
        "const",         CONST;
        "else",          ELSE;
        "elsif",         ELSIF;
        "end",           END;
        "if",            IF;
        "implements",    IMPLEMENTS;
        "imported",      IMPORTED;
        "is",            IS;
        "loop",          LOOP;
        "new",           NEW;
        "not",           NOT;
        "or",            OR;
        "out",           OUT;
        "overriding",    OVERRIDING;
        "proc",          PROC;
        "return",        RETURN;
        "then",          THEN;
        "type",          TYPE;
        "unit",          UNIT;
        "var",           VAR;
        "virtual",       VIRTUAL;
        "while",         WHILE;
        "with",          WITH;
    ]
}

rule scan = parse
    [' ' '\t']          { scan lexbuf }
  | '\n'                { Lexing.new_line lexbuf; scan lexbuf }
  | "--" [^ '\n']* '\n' { Lexing.new_line lexbuf; scan lexbuf }
  | ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']* as id
        { try Hashtbl.find keywords id
          with Not_found -> IDENT(id) }
  | '"' ([^ '"']* as text) '"'    { STRING(text) }
  | '\'' ([^ '\'']* as text) '\''     { CHARLIT(text) }
  | ['0'-'9']+ as value { INTEGER(big_int_of_string value) }
  | '('  { LPAREN }
  | ')'  { RPAREN }
  | '{'  { LBRACE }
  | '}'  { RBRACE }
  | '?'  { QUESTION }
  | ':'  { COLON }
  | ';'  { SEMICOLON }
  | '.'  { DOT }
  | ','  { COMMA }
  | '^'  { CARET }
  | '+'  { PLUS }
  | '-'  { DASH }
  | '*'  { STAR }
  | '/'  { SLASH }
  | '|'  { MID }
  | ":=" { ASSIGN }
  | ".." { DOTDOT }
  | '='  { EQ }
  | "<>" { NE }
  | '<'  { LT }
  | '>'  { GT }
  | "<=" { LE }
  | ">=" { GE }
  | "=>" { ARROW }
  | eof  { EOF }
