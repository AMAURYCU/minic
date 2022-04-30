(* Représentation des types. *)
type typ =
  | Int
  | Bool
  | Void
  |String
  |Float

(* Représentation des expressions.
   Ajouté : les constantes booléennes. *)
type expr =
  | Cst of int
  | BCst of bool
  |SCst of string
  |FCst of float
  | Empty
  | Add of expr * expr
  | Mul of expr * expr
  | Div of expr * expr 
  | Lt  of expr * expr  (* < *)
  | LtEq of expr * expr (* <= *)
  | Gt of expr * expr  (* > *)
  | GtEq of expr * expr  (* >= *)
  | Eq of expr * expr (* == *)
  | Opos of expr (* - (nombre opposé) *)
  | Not of expr (* ! *)
  | And of expr * expr (* && *)
  | Or of expr * expr (* || *)
  | Get of string
  | Call of string * expr list
  | Epar of expr (* (e) *)
  | EComma of expr  (* e, *)
  |Pow of expr * expr(*x^n*)
  | Concat of expr * expr(*"abc" *)

(* Représentation des instructions et séquences. *)
type instr =
  | Putchar of expr
  | Set of string * expr
  | AddSet of string * expr (* += *)
  | If  of expr * seq * seq
  | While of expr * seq
  | Return of expr
  | Expr of expr
  | For of instr * expr * instr * seq
and seq = instr list

(* Représentétion des fonctions. *)
type fun_def = {
  name: string;
  params: (string * typ * expr) list;
  return: typ;
  locals: (string * typ * expr ) list;
  code: seq;
}

type tab_def = {
  identity: string;
  type_elements: typ;
  length: int;
  content: expr list;
}

(* Représentation des programmes.
   En réponse à l'indication de l'énoncé, j'associe une valeur entière
   à chaque variable globale. Mais vous voudrez peut-être faire évoluer
   cela (et procéder de même pour les variables locales des fonctions). *)
type prog = {
  globals: (string * typ * expr) list;
  tables: tab_def list;
  functions: fun_def list;
}
