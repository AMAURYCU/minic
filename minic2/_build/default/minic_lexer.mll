{

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
        
}

(* Règles auxiliaires *)
let digit = ['0'-'9']
let number = ['-']? digit+
let alpha = ['a'-'z' 'A'-'Z']
let accent = ("e"|"è"|"ê"|"à"|"ç")
let ident = alpha (alpha | '_' | digit)*
let stri = '"' (alpha|accent|digit|' ')+ '"'
let flo = digit* '.' digit+
(* Règles de reconnaissance 
   À COMPLÉTER
*)
rule token = parse
  | ['\n']
      { new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r']+
      { token lexbuf }
  | number as n
      { CST(int_of_string n) }
  | ident as id
      { keyword_or_ident id }
    |flo as f
        {FCST(float_of_string f)}
  | ";"
      { SEMI }
  | ","
      { COMMA }
  | "="
      { SET }
  | "("
      { LPAR }
  | ")"
      { RPAR }
  | "{"
      { BEGIN }
  | "}"
      { END }
  | "["
      { LBRACKET }
  | "]"
      { RBRACKET }
  | "+"
        { ADD }
  | "*"
        { MUL }
  | "/"
        { DIV }
  | "<"
        { LT }
  | "<="
        { LTEQ }
  | ">"
        { GT }
  | ">="
        { GTEQ }
  | "=="
        { EQ }
  | "-"
        { OPOS }
  | "+="
        { ADDSET }
  | "!"
        { NOT }
  | "&&"
        { AND }
  | "||"
        { OR }
| "^"
    {POW} 
|"@@"
    {CONC}
| stri as s 
    {STR(s)}
  | _
      { failwith ("Unknown character : " ^ (lexeme lexbuf)) }
  | eof
      { EOF }