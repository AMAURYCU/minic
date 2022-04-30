
(* The type of tokens. *)

type token = 
  | WHILE
  | VOID
  | TAB
  | STRING
  | STR of (string)
  | SET
  | SEMI
  | RPAR
  | RETURN
  | RBRACKET
  | PUTCHAR
  | POW
  | OR
  | OPOS
  | NOT
  | MUL
  | LTEQ
  | LT
  | LPAR
  | LBRACKET
  | INT
  | IF
  | IDENT of (string)
  | GTEQ
  | GT
  | FOR
  | FLOAT
  | FCST of (float)
  | EQ
  | EOF
  | END
  | ELSE
  | DIV
  | CST of (int)
  | CONC
  | COMMA
  | BOOL_CST of (bool)
  | BOOL
  | BEGIN
  | AND
  | ADDSET
  | ADD

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val program: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Minic_ast.prog)
