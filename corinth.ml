let try_parse f lexbuf =
    try
        f Lexer.scan lexbuf
    with Parsing.Parse_error ->
        prerr_endline (Errors.string_of_location
            (Lexing.lexeme_start_p lexbuf)
            ^ ": Syntax error.");
        raise (Failure "Syntax error.")
let _ =
    let input_name = Sys.argv.(1) in
    let f = open_in input_name in
    let lexbuf = Lexing.from_channel f in
    lexbuf.Lexing.lex_curr_p <- {
        lexbuf.Lexing.lex_curr_p with
        Lexing.pos_fname = input_name
    };

    let root_sym = Symtab.new_root_symbol () in
    let unit = try_parse Parser.unit_decl lexbuf in
    let ts = Translate.new_translation_state root_sym in
    Translate.trans_unit ts unit;
    Translate.finish_trans ts

