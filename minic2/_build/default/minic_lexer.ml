# 1 "minic_lexer.mll"
 

  open Lexing
  open Minic_parser

  (* Fonction auxiliaire pour rassembler les mots-clés 
     À COMPLÉTER
   *)
  let keyword_or_ident =
    let h = Hashtbl.create 17 in
    List.iter (fun (s, k) -> Hashtbl.add h s k)
      [ "return",   RETURN;
        "true",     BOOL_CST true;
        "false",    BOOL_CST false; (*NEW*)
        "bool",     BOOL;
        "int",      INT;
        "void",     VOID; (*NEW*)
        "float",    FLOAT;
        "putchar",  PUTCHAR; (*NEW*)
        "if",       IF; (*NEW*)
        "else",     ELSE; (*NEW*)
        "while",    WHILE; (*NEW*)
        "for",      FOR; (*NEW*)
        "tab",      TAB;
        "string",    STRING;
     
      ] ;
    fun s ->
      try  Hashtbl.find h s
      with Not_found -> IDENT(s)
        

# 35 "minic_lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\224\255\225\255\094\000\028\000\228\255\003\000\001\000\
    \231\255\002\000\034\000\239\255\240\255\035\000\242\255\243\255\
    \244\255\245\255\246\255\247\255\067\000\249\255\250\255\081\000\
    \193\000\171\000\181\000\003\000\255\255\012\001\022\001\032\001\
    \234\255\232\255\237\255\235\255\230\255\229\255\227\255\058\001\
    \187\000\226\255";
  Lexing.lex_backtrk =
   "\255\255\255\255\255\255\030\000\030\000\255\255\030\000\030\000\
    \255\255\019\000\017\000\255\255\255\255\014\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\007\000\255\255\255\255\030\000\
    \003\000\002\000\022\000\001\000\255\255\002\000\255\255\004\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255";
  Lexing.lex_default =
   "\002\000\000\000\000\000\255\255\255\255\000\000\255\255\255\255\
    \000\000\255\255\255\255\000\000\000\000\255\255\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\000\000\000\000\255\255\
    \255\255\255\255\255\255\255\255\000\000\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\255\255\
    \255\255\000\000";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\027\000\028\000\000\000\027\000\027\000\000\000\000\000\
    \027\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \027\000\008\000\003\000\027\000\000\000\000\000\007\000\036\000\
    \019\000\018\000\012\000\013\000\021\000\026\000\023\000\011\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\000\000\022\000\010\000\020\000\009\000\035\000\
    \004\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\015\000\038\000\014\000\005\000\034\000\
    \033\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\017\000\006\000\016\000\039\000\037\000\
    \032\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\000\000\000\000\000\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\000\000\000\000\000\000\000\000\000\000\000\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\030\000\000\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\029\000\000\000\
    \000\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\000\000\000\000\000\000\000\000\000\000\
    \001\000\000\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\000\000\000\000\000\000\000\000\
    \024\000\040\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\039\000\039\000\041\000\000\000\000\000\000\000\
    \000\000\000\000\039\000\039\000\000\000\039\000\000\000\000\000\
    \000\000\000\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\040\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\255\255\027\000\000\000\255\255\255\255\
    \027\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\027\000\255\255\255\255\000\000\007\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\255\255\000\000\000\000\000\000\000\000\009\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\004\000\000\000\000\000\010\000\
    \013\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\003\000\006\000\
    \020\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\255\255\255\255\255\255\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\255\255\255\255\255\255\255\255\255\255\255\255\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\025\000\255\255\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\026\000\026\000\026\000\
    \026\000\026\000\026\000\026\000\026\000\026\000\026\000\255\255\
    \255\255\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\255\255\255\255\255\255\255\255\
    \024\000\003\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\029\000\029\000\029\000\029\000\
    \029\000\029\000\029\000\029\000\029\000\029\000\030\000\030\000\
    \030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
    \031\000\031\000\031\000\031\000\031\000\031\000\031\000\031\000\
    \031\000\031\000\039\000\040\000\039\000\255\255\255\255\255\255\
    \255\255\255\255\040\000\040\000\255\255\040\000\255\255\255\255\
    \255\255\255\255\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
    \039\000\039\000\039\000\039\000\039\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\039\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255";
  Lexing.lex_base_code =
   "";
  Lexing.lex_backtrk_code =
   "";
  Lexing.lex_default_code =
   "";
  Lexing.lex_trans_code =
   "";
  Lexing.lex_check_code =
   "";
  Lexing.lex_code =
   "";
}

let rec token lexbuf =
   __ocaml_lex_token_rec lexbuf 0
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 47 "minic_lexer.mll"
      ( new_line lexbuf; token lexbuf )
# 225 "minic_lexer.ml"

  | 1 ->
# 49 "minic_lexer.mll"
      ( token lexbuf )
# 230 "minic_lexer.ml"

  | 2 ->
let
# 50 "minic_lexer.mll"
              n
# 236 "minic_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 51 "minic_lexer.mll"
      ( CST(int_of_string n) )
# 240 "minic_lexer.ml"

  | 3 ->
let
# 52 "minic_lexer.mll"
             id
# 246 "minic_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 53 "minic_lexer.mll"
      ( keyword_or_ident id )
# 250 "minic_lexer.ml"

  | 4 ->
let
# 54 "minic_lexer.mll"
            f
# 256 "minic_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 55 "minic_lexer.mll"
        (FCST(float_of_string f))
# 260 "minic_lexer.ml"

  | 5 ->
# 57 "minic_lexer.mll"
      ( SEMI )
# 265 "minic_lexer.ml"

  | 6 ->
# 59 "minic_lexer.mll"
      ( COMMA )
# 270 "minic_lexer.ml"

  | 7 ->
# 61 "minic_lexer.mll"
      ( SET )
# 275 "minic_lexer.ml"

  | 8 ->
# 63 "minic_lexer.mll"
      ( LPAR )
# 280 "minic_lexer.ml"

  | 9 ->
# 65 "minic_lexer.mll"
      ( RPAR )
# 285 "minic_lexer.ml"

  | 10 ->
# 67 "minic_lexer.mll"
      ( BEGIN )
# 290 "minic_lexer.ml"

  | 11 ->
# 69 "minic_lexer.mll"
      ( END )
# 295 "minic_lexer.ml"

  | 12 ->
# 71 "minic_lexer.mll"
      ( LBRACKET )
# 300 "minic_lexer.ml"

  | 13 ->
# 73 "minic_lexer.mll"
      ( RBRACKET )
# 305 "minic_lexer.ml"

  | 14 ->
# 75 "minic_lexer.mll"
        ( ADD )
# 310 "minic_lexer.ml"

  | 15 ->
# 77 "minic_lexer.mll"
        ( MUL )
# 315 "minic_lexer.ml"

  | 16 ->
# 79 "minic_lexer.mll"
        ( DIV )
# 320 "minic_lexer.ml"

  | 17 ->
# 81 "minic_lexer.mll"
        ( LT )
# 325 "minic_lexer.ml"

  | 18 ->
# 83 "minic_lexer.mll"
        ( LTEQ )
# 330 "minic_lexer.ml"

  | 19 ->
# 85 "minic_lexer.mll"
        ( GT )
# 335 "minic_lexer.ml"

  | 20 ->
# 87 "minic_lexer.mll"
        ( GTEQ )
# 340 "minic_lexer.ml"

  | 21 ->
# 89 "minic_lexer.mll"
        ( EQ )
# 345 "minic_lexer.ml"

  | 22 ->
# 91 "minic_lexer.mll"
        ( OPOS )
# 350 "minic_lexer.ml"

  | 23 ->
# 93 "minic_lexer.mll"
        ( ADDSET )
# 355 "minic_lexer.ml"

  | 24 ->
# 95 "minic_lexer.mll"
        ( NOT )
# 360 "minic_lexer.ml"

  | 25 ->
# 97 "minic_lexer.mll"
        ( AND )
# 365 "minic_lexer.ml"

  | 26 ->
# 99 "minic_lexer.mll"
        ( OR )
# 370 "minic_lexer.ml"

  | 27 ->
# 101 "minic_lexer.mll"
    (POW)
# 375 "minic_lexer.ml"

  | 28 ->
# 103 "minic_lexer.mll"
    (CONC)
# 380 "minic_lexer.ml"

  | 29 ->
let
# 104 "minic_lexer.mll"
          s
# 386 "minic_lexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 105 "minic_lexer.mll"
    (STR(s))
# 390 "minic_lexer.ml"

  | 30 ->
# 107 "minic_lexer.mll"
      ( failwith ("Unknown character : " ^ (lexeme lexbuf)) )
# 395 "minic_lexer.ml"

  | 31 ->
# 109 "minic_lexer.mll"
      ( EOF )
# 400 "minic_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_token_rec lexbuf __ocaml_lex_state

;;
