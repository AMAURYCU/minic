%{

  open Lexing
  open Minic_ast
    let rec optim = function
|Add(e1, e2) ->
let ep = optim e1 in
let esec = optim e2 in
begin match ep, esec with
| Cst n1, Cst n2 -> Cst (n1 + n2)
| FCst n1, FCst n2 -> FCst(n1+.n2)
|FCst n1, Cst n2 -> FCst(n1+.(float_of_int n2))
|Cst n1 , FCst n2 -> FCst((float_of_int n1)+.n2)
| _, _ -> Add(ep, esec)
end
|Mul(e1,e2) ->let ep = optim e1 in
let esec = optim e2 in
begin match ep, esec with
| Cst n1, Cst n2 -> Cst (n1 * n2)
| FCst n1, FCst n2 -> FCst(n1*.n2)
|FCst n1, Cst n2 -> FCst( n1*. (float_of_int n2))
|Cst n1 , FCst n2 -> FCst((float_of_int n1)*.n2)
| _, _ -> Mul(ep, esec)
end

|Div(e1,e2) -> let ep = optim e1 in
let esec = optim e2 in
begin match ep, esec with
| Cst n1, Cst n2 -> Cst (n1 / n2)
| FCst n1, FCst n2 -> FCst(n1/.n2)
|FCst n1, Cst n2 -> FCst(n1/.(float_of_int n2))
|Cst n1 , FCst n2 -> FCst((float_of_int n1)/.n2)
| _, _ -> Div(ep, esec)
end
|Lt(e1,e2) -> let ep = optim e1 in let esec = optim e2 
in  begin match ep,esec with 
|Cst n1, Cst n2 -> BCst(n1<n2)
| _,_ -> Lt(ep,esec)
 end 
|LtEq(e1,e2) -> let ep = optim e1 in let esec = optim e2 
in  begin match ep,esec with 
|Cst n1, Cst n2 -> BCst(n1 <= n2)
| _,_ -> LtEq(ep,esec) 
end
| Gt(e1,e2) -> let ep = optim e1 in let esec = optim e2 
in  begin match ep,esec with 
|Cst n1, Cst n2 -> BCst(n1 > n2)
| _,_ -> Gt(ep,esec) 
end
| GtEq(e1,e2) -> let ep = optim e1 in let esec = optim e2 
in  begin match ep,esec with 
|Cst n1, Cst n2 -> BCst(n1 >= n2)
| _,_ -> GtEq(ep,esec) 
end
| Eq(e1,e2)-> let ep = optim e1 in let esec = optim e2 
in  begin match ep,esec with 
|Cst n1, Cst n2 -> BCst(n1 == n2)
| _,_ -> Eq(ep,esec) 
end
| Opos(e) -> let ep = optim e in 
begin match ep with 
|Cst n -> Cst(-n)
|FCst n -> FCst(0.-.n)
| _ -> Opos(ep)
end
|Not(e) -> let ep = optim e in 
begin match ep with 
|BCst n -> BCst(n)
| _ -> Not(ep)
end
|Or(e1,e2) -> let ep = optim e1 in let esec = optim e2 in
begin match ep, esec with 
|BCst(n1), BCst(n2)-> BCst(n1 || n2)
| _,_ -> Or(ep,esec)
end
|And(e1,e2)->let ep = optim e1 in let esec = optim e2 in
begin match ep, esec with 
|BCst(n1), BCst(n2)-> BCst(n1 && n2)
| _,_ -> And(ep,esec)
end
|Epar(e) -> Epar(optim(e))
|EComma(e)-> EComma(optim(e))
|Call(f,v) -> let vopt = List.map optim v in Call(f,vopt)
| Empty -> Empty
|Cst(n)-> Cst(n)
|BCst(n) -> BCst(n)
|Get(x) -> Get(x)
|FCst(n) -> FCst(n)
|Pow(e1,e2)-> let ep = optim e1 in
let esec = optim e2 in
begin match ep, esec with
| Cst n1, Cst n2 -> FCst ((float_of_int n1) **(float_of_int  n2))
| FCst n1, FCst n2 -> FCst(n1**n2)
|FCst n1, Cst n2 -> FCst(n1**(float_of_int n2))
|Cst n1 , FCst n2 -> FCst((float_of_int n1)**n2)
| _, _ -> Pow(ep, esec)
end
|Concat(e1,e2) -> let oe1 = optim e1 in let oe2 = optim e2 in begin match oe1,oe2 with 
|SCst n1 , SCst n2 -> SCst(n1^n2)
|_,_ -> Concat(oe1,oe2) end
|SCst n -> SCst(n)
|GetTab(a,b)-> GetTab(a,b)
|SetTab(a,b)-> SetTab(a,b)
            
%}

(* Déclaration des lexèmes *)
%token <int> CST
%token <bool> BOOL_CST
%token <string> IDENT STR
%token <float> FCST
%token LPAR RPAR BEGIN END LBRACKET RBRACKET
%token ADD MUL DIV LT LTEQ GT GTEQ EQ OPOS NOT AND OR
%token RETURN SET ADDSET
%token SEMI COMMA
%token INT BOOL VOID TAB STRING FLOAT
%token EOF
%token PUTCHAR (*NEW - Putchar of expr*)
%token IF ELSE (*NEW - If of expr * seq * seq *)
%token WHILE (*NEW - While of expr * seq *)
%token FOR 
%token POW CONC

%left IDENT
%left LPAR
%left LT GT
%left LTEQ GTEQ
%left EQ
%left OR AND
%left ADD
%left MUL DIV
%left POW
%left CONC

%nonassoc NOT OPOS


%start program
%type <Minic_ast.prog> program

%%

(* Un programme est une liste de déclarations.
   On ajoute une règle déclenchée en cas d'erreur, donnant une
   information minimale : la position. *)
program:
| dl=declaration_list EOF
       { let var_list, tab_list, fun_list = dl in
         { globals = var_list; tables = tab_list; functions = fun_list; } }
| error { let pos = $startpos in
          let message =
            Printf.sprintf
              "Syntax error at %d, %d"
              pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
          in
          failwith message }
;

(* Chaque déclaration peut concerner une variable ou une fonction. *)
declaration_list:
| (* vide *) { [], [], [] }    
| vd=variable_decl dl=declaration_list { let vl, tl, fl = dl in
                                         vd :: vl, tl, fl }
| td=tab_decl dl=declaration_list { let vl, tl, fl = dl in
                                         vl, td :: tl, fl }
| fd=function_decl dl=declaration_list { let vl, tl, fl = dl in
                                         vl, tl, fd :: fl }
;

(* Déclaration de variable.
   Note : on ne traite ici que le cas où une valeur initiale est fournie.

   À COMPLÉTER
*)
variable_decl:
| typ IDENT SET expression { failwith "Missing semicolon after variable declaration" } (*NEW*)
| typ IDENT { failwith "Missing semicolon after variable declaration" } (*NEW*)
| t=typ x=IDENT SET e=expression SEMI { (x, t, e) } (*NEW*)
| t=typ x=IDENT SEMI { (x, t, Empty) } (*NEW*)

tab_decl:
| TAB LPAR typ RPAR IDENT LBRACKET CST RBRACKET SET BEGIN separated_list(COMMA, expression) END
{ failwith "Missing semicolon after table declaration" }
| TAB LPAR typ RPAR IDENT LBRACKET CST RBRACKET
{ failwith "Missing semicolon after table declaration" }
| TAB LPAR t=typ RPAR x=IDENT LBRACKET n=CST RBRACKET SET BEGIN le = separated_list(COMMA, expression) END SEMI
{ { identity=x; type_elements=t; length=n; content=le} }
| TAB LPAR t=typ RPAR x=IDENT LBRACKET n=CST RBRACKET SEMI
{ { identity=x; type_elements=t; length=n; content=[]} }
;

(*Declaration de variable sans point virgule pour les param de fonctions*)
param_decl:
| t=typ x=IDENT SET e=expression { (x, t, e) } (*NEW*)
| t=typ x=IDENT { (x, t, Empty) } (*NEW*)
;

(* Indication de type.

   À COMPLÉTER
*)
typ:
| INT { Int }
| BOOL { Bool }
| VOID {Void}
| STRING {String}
| FLOAT {Float}
;

(* Déclaration de fonction.
   Note : on ne traite ici que le cas d'une fonction sans argument et
   sans variable locale.

   À COMPLÉTER
*)
function_decl:
| t=typ f=IDENT LPAR p=separated_list(COMMA, param_decl) RPAR BEGIN v=list(variable_decl) s=list(instruction) END (*la declaration des variables locales se fait avant la seq d'instr*)
    { { name=f; code=s; params=p; return=t; locals=v } }
;

(* Instructions.

   À COMPLÉTER
*)
instruction:
| RETURN expression { failwith "Missing semicolon after 'return'" }
| PUTCHAR LPAR expression RPAR { failwith "Missing semicolon after 'putchar'" } (*NEW*)
| IDENT SET expression { failwith "Missing semicolon after value assignment '='" } (*NEW*)
| IDENT ADDSET expression { failwith "Missing semicolon after value assignment '+='" }
| RETURN e=expression SEMI { Return(e) }
| PUTCHAR LPAR e=expression RPAR SEMI { Putchar(e) } (*NEW*)
| IF LPAR c=expression RPAR BEGIN s1=list(instruction) END ELSE BEGIN s2=list(instruction) END { If(c, s1, s2) } (*NEW*)
| WHILE LPAR c=expression RPAR BEGIN s=list(instruction) END { While(c, s) } (*NEW*)
| FOR LPAR init=instruction_for SEMI cond=expression SEMI incr=instruction_for RPAR BEGIN s=list(instruction) END { For(init, cond, incr, s) } (*Nous detectons les boucles FOR de la forme for(init;incr;cond){seq;}*)
| x = IDENT SET e=expression SEMI { Set(x,e)} (*NEW*)
| x = IDENT ADDSET e = expression SEMI { AddSet(x,e) }
| e = expression { Expr(e) }
;

instruction_for:
| x = IDENT SET e=expression { Set(x,e)}
| x = IDENT ADDSET e = expression { AddSet(x,e) }


(* Expressions.

   À COMPLÉTER
*)
expression:
| n=CST { Cst(n) }
| b=BOOL_CST { BCst(b) }
| s = STR {SCst(s)}
| f = FCST{FCst(f)}
| e1 = expression ADD e2 = expression { optim(Add(e1,e2)) }
| e1 = expression MUL e2 = expression { optim (Mul(e1,e2) )}
| e1 = expression DIV e2 = expression { optim (Div(e1,e2)) } 
| e1 = expression LT e2 = expression {optim (Lt(e1,e2)) }
| e1 = expression LTEQ e2 = expression {optim(LtEq(e1,e2)) }
| e1 = expression GT e2 = expression { optim (Gt(e1,e2)) }
| e1 = expression GTEQ e2 = expression { optim (GtEq(e1,e2)) }
| e1 = expression EQ e2 = expression { optim (Eq(e1,e2)) }
| OPOS e = expression {optim ( Opos(e)) }
| NOT e = expression { optim (Not(e))}
| e1 = expression OR e2 = expression { optim(Or(e1,e2)) }
| e1 = expression AND e2 = expression { optim(And(e1,e2) )}
| x=IDENT { Get(x)} (*Acces à une var*)
| f=IDENT LPAR v = separated_list(COMMA, expression) RPAR { optim(Call (f, v))} (*Appel à une fct avec param*)
| LPAR e = expression RPAR {optim( Epar(e) )}
|e1 = expression POW e2 = expression { Pow(e1,e2)}
|e1 = expression CONC e2 = expression {Concat(e1,e2)}

;

