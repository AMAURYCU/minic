
module MenhirBasics = struct
  
  exception Error
  
  let _eRR : exn =
    Error
  
  type token = 
    | WHILE
    | VOID
    | TAB
    | STRING
    | STR of (
# 108 "minic_parser.mly"
       (string)
# 18 "minic_parser.ml"
  )
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
    | IDENT of (
# 108 "minic_parser.mly"
       (string)
# 40 "minic_parser.ml"
  )
    | GTEQ
    | GT
    | FOR
    | FLOAT
    | FCST of (
# 109 "minic_parser.mly"
       (float)
# 49 "minic_parser.ml"
  )
    | EQ
    | EOF
    | END
    | ELSE
    | DIV
    | CST of (
# 106 "minic_parser.mly"
       (int)
# 59 "minic_parser.ml"
  )
    | CONC
    | COMMA
    | BOOL_CST of (
# 107 "minic_parser.mly"
       (bool)
# 66 "minic_parser.ml"
  )
    | BOOL
    | BEGIN
    | AND
    | ADDSET
    | ADD
  
end

include MenhirBasics

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState143
  | MenhirState142
  | MenhirState135
  | MenhirState129
  | MenhirState126
  | MenhirState123
  | MenhirState121
  | MenhirState118
  | MenhirState116
  | MenhirState114
  | MenhirState110
  | MenhirState107
  | MenhirState105
  | MenhirState102
  | MenhirState97
  | MenhirState93
  | MenhirState92
  | MenhirState89
  | MenhirState87
  | MenhirState83
  | MenhirState82
  | MenhirState78
  | MenhirState74
  | MenhirState71
  | MenhirState67
  | MenhirState64
  | MenhirState54
  | MenhirState52
  | MenhirState50
  | MenhirState48
  | MenhirState46
  | MenhirState44
  | MenhirState42
  | MenhirState40
  | MenhirState38
  | MenhirState36
  | MenhirState34
  | MenhirState32
  | MenhirState30
  | MenhirState22
  | MenhirState20
  | MenhirState19
  | MenhirState18
  | MenhirState16
  | MenhirState4
  | MenhirState0

# 1 "minic_parser.mly"
  

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
            

# 237 "minic_parser.ml"

[@@@ocaml.warning "-4-39"]

let rec _menhir_goto_list_instruction_ :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (Minic_ast.seq) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState126 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((((_menhir_stack, _menhir_s), _, (init : (Minic_ast.instr))), _, (cond : (Minic_ast.expr))), _, (incr : (Minic_ast.instr))), _, (s : (Minic_ast.seq))) = _menhir_stack in
            let _v : (Minic_ast.instr) = 
# 232 "minic_parser.mly"
                                                                                                                  ( For(init, cond, incr, s) )
# 258 "minic_parser.ml"
             in
            _menhir_goto_instruction _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (Minic_ast.instr))), _, (xs : (Minic_ast.seq))) = _menhir_stack in
        let _v : (Minic_ast.seq) = 
# 210 "<standard.mly>"
    ( x :: xs )
# 274 "minic_parser.ml"
         in
        _menhir_goto_list_instruction_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | ELSE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BEGIN ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | BOOL_CST _v ->
                        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
                    | CST _v ->
                        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
                    | FCST _v ->
                        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
                    | FOR ->
                        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState135
                    | IDENT _v ->
                        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
                    | IF ->
                        _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState135
                    | LPAR ->
                        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState135
                    | NOT ->
                        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState135
                    | OPOS ->
                        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState135
                    | PUTCHAR ->
                        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState135
                    | RETURN ->
                        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState135
                    | STR _v ->
                        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
                    | WHILE ->
                        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState135
                    | END ->
                        _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState135
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState135)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState135 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((((_menhir_stack, _menhir_s), _, (c : (Minic_ast.expr))), _, (s1 : (Minic_ast.seq))), _, (s2 : (Minic_ast.seq))) = _menhir_stack in
            let _v : (Minic_ast.instr) = 
# 230 "minic_parser.mly"
                                                                                               ( If(c, s1, s2) )
# 360 "minic_parser.ml"
             in
            _menhir_goto_instruction _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s), _, (c : (Minic_ast.expr))), _, (s : (Minic_ast.seq))) = _menhir_stack in
            let _v : (Minic_ast.instr) = 
# 231 "minic_parser.mly"
                                                             ( While(c, s) )
# 382 "minic_parser.ml"
             in
            _menhir_goto_instruction _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState87 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((((_menhir_stack, _menhir_s, (t : (Minic_ast.typ))), (f : (
# 108 "minic_parser.mly"
       (string)
# 403 "minic_parser.ml"
            ))), _, (xs : ((string * Minic_ast.typ * Minic_ast.expr) list))), _, (v : ((string * Minic_ast.typ * Minic_ast.expr) list))), _, (s : (Minic_ast.seq))) = _menhir_stack in
            let _v =
              let p = 
# 229 "<standard.mly>"
    ( xs )
# 409 "minic_parser.ml"
               in
              (
# 216 "minic_parser.mly"
    ( { name=f; code=s; params=p; return=t; locals=v } )
# 414 "minic_parser.ml"
               : (Minic_ast.fun_def))
            in
            let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_stack = Obj.magic _menhir_stack in
            assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | FLOAT ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | INT ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | STRING ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | TAB ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | VOID ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | EOF ->
                _menhir_reduce1 _menhir_env (Obj.magic _menhir_stack) MenhirState143
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_list_variable_decl_ :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * Minic_ast.typ * Minic_ast.expr) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (x : (string * Minic_ast.typ * Minic_ast.expr))), _, (xs : ((string * Minic_ast.typ * Minic_ast.expr) list))) = _menhir_stack in
        let _v : ((string * Minic_ast.typ * Minic_ast.expr) list) = 
# 210 "<standard.mly>"
    ( x :: xs )
# 460 "minic_parser.ml"
         in
        _menhir_goto_list_variable_decl_ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL_CST _v ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
        | CST _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
        | FCST _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
        | FOR ->
            _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | IDENT _v ->
            _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
        | IF ->
            _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | LPAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | NOT ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | OPOS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | PUTCHAR ->
            _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | RETURN ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | STR _v ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState87 _v
        | WHILE ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | END ->
            _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState87
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState87)
    | _ ->
        _menhir_fail ()

and _menhir_run115 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 108 "minic_parser.mly"
       (string)
# 506 "minic_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ADDSET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL_CST _v ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
        | CST _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
        | FCST _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
        | IDENT _v ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
        | LPAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState118
        | NOT ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState118
        | OPOS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState118
        | STR _v ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState118)
    | SET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL_CST _v ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
        | CST _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
        | FCST _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
        | IDENT _v ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
        | LPAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState116
        | NOT ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState116
        | OPOS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState116
        | STR _v ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_instruction_for :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (Minic_ast.instr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState114 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL_CST _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
            | CST _v ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
            | FCST _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
            | IDENT _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
            | LPAR ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | NOT ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | OPOS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState121
            | STR _v ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState121)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState123 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BEGIN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BOOL_CST _v ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState126 _v
                | CST _v ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState126 _v
                | FCST _v ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState126 _v
                | FOR ->
                    _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState126
                | IDENT _v ->
                    _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState126 _v
                | IF ->
                    _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState126
                | LPAR ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState126
                | NOT ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState126
                | OPOS ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState126
                | PUTCHAR ->
                    _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState126
                | RETURN ->
                    _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState126
                | STR _v ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState126 _v
                | WHILE ->
                    _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState126
                | END ->
                    _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState126
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState126)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_instruction :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (Minic_ast.instr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _v
    | FOR ->
        _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState129
    | IDENT _v ->
        _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _v
    | IF ->
        _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState129
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState129
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState129
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState129
    | PUTCHAR ->
        _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState129
    | RETURN ->
        _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState129
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState129 _v
    | WHILE ->
        _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState129
    | END ->
        _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState129
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState129

and _menhir_reduce41 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Minic_ast.seq) = 
# 208 "<standard.mly>"
    ( [] )
# 717 "minic_parser.ml"
     in
    _menhir_goto_list_instruction_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run88 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL_CST _v ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
        | CST _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
        | FCST _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
        | IDENT _v ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
        | LPAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | NOT ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | OPOS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState89
        | STR _v ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState89 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState89)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run93 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93

and _menhir_run96 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL_CST _v ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
        | CST _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
        | FCST _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
        | IDENT _v ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
        | LPAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState97
        | NOT ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState97
        | OPOS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState97
        | STR _v ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState97 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState97)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run101 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL_CST _v ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
        | CST _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
        | FCST _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
        | IDENT _v ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
        | LPAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState102
        | NOT ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState102
        | OPOS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState102
        | STR _v ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState102)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run106 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 108 "minic_parser.mly"
       (string)
# 865 "minic_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ADDSET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL_CST _v ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
        | CST _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
        | FCST _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
        | IDENT _v ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
        | LPAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | NOT ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | OPOS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState110
        | STR _v ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState110)
    | LPAR ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack)
    | SET ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL_CST _v ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v
        | CST _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v
        | FCST _v ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v
        | IDENT _v ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v
        | LPAR ->
            _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState107
        | NOT ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState107
        | OPOS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState107
        | STR _v ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState107 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState107)
    | ADD | AND | BOOL_CST _ | CONC | CST _ | DIV | END | EQ | FCST _ | FOR | GT | GTEQ | IDENT _ | IF | LT | LTEQ | MUL | NOT | OPOS | OR | POW | PUTCHAR | RETURN | STR _ | WHILE ->
        _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run113 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT _v ->
            _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState114 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState114)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_goto_separated_nonempty_list_COMMA_expression_ :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (Minic_ast.expr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState16 | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : (Minic_ast.expr list)) = _v in
        let _v : (Minic_ast.expr list) = 
# 141 "<standard.mly>"
    ( x )
# 967 "minic_parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_expression__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : (Minic_ast.expr list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (Minic_ast.expr))) = _menhir_stack in
        let _v : (Minic_ast.expr list) = 
# 240 "<standard.mly>"
    ( x :: xs )
# 978 "minic_parser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_expression_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_run30 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState30 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState30 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState30 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState30 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState30
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState30
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState30
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState30 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState30

and _menhir_run34 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState34
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState34 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState34

and _menhir_run36 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState36
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState36
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState36
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState36 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState36

and _menhir_run42 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState42
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState42
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState42
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42

and _menhir_run48 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState48
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState48
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState48
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState48 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState48

and _menhir_run50 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState50
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50

and _menhir_run52 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState52
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState52
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState52
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState52 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState52

and _menhir_run44 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState44
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState44
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState44
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44

and _menhir_run38 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState38
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38

and _menhir_run32 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState32
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState32
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState32
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState32 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState32

and _menhir_run46 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState46
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState46
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState46
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46

and _menhir_run40 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState40
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState40
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState40
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40

and _menhir_goto_separated_nonempty_list_COMMA_param_decl_ :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * Minic_ast.typ * Minic_ast.expr) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (x : ((string * Minic_ast.typ * Minic_ast.expr) list)) = _v in
        let _v : ((string * Minic_ast.typ * Minic_ast.expr) list) = 
# 141 "<standard.mly>"
    ( x )
# 1306 "minic_parser.ml"
         in
        _menhir_goto_loption_separated_nonempty_list_COMMA_param_decl__ _menhir_env _menhir_stack _menhir_s _v
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let (xs : ((string * Minic_ast.typ * Minic_ast.expr) list)) = _v in
        let (_menhir_stack, _menhir_s, (x : (string * Minic_ast.typ * Minic_ast.expr))) = _menhir_stack in
        let _v : ((string * Minic_ast.typ * Minic_ast.expr) list) = 
# 240 "<standard.mly>"
    ( x :: xs )
# 1317 "minic_parser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_param_decl_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        _menhir_fail ()

and _menhir_goto_variable_decl :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (string * Minic_ast.typ * Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState143 | MenhirState142 | MenhirState64 | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | FLOAT ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | INT ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | STRING ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | TAB ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | EOF ->
            _menhir_reduce1 _menhir_env (Obj.magic _menhir_stack) MenhirState64
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState64)
    | MenhirState83 | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState83
        | FLOAT ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState83
        | INT ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState83
        | STRING ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState83
        | VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState83
        | BOOL_CST _ | CST _ | END | FCST _ | FOR | IDENT _ | IF | LPAR | NOT | OPOS | PUTCHAR | RETURN | STR _ | WHILE ->
            _menhir_reduce43 _menhir_env (Obj.magic _menhir_stack) MenhirState83
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState83)
    | _ ->
        _menhir_fail ()

and _menhir_reduce43 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : ((string * Minic_ast.typ * Minic_ast.expr) list) = 
# 208 "<standard.mly>"
    ( [] )
# 1379 "minic_parser.ml"
     in
    _menhir_goto_list_variable_decl_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_loption_separated_nonempty_list_COMMA_expression__ :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (Minic_ast.expr list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (f : (
# 108 "minic_parser.mly"
       (string)
# 1399 "minic_parser.ml"
            ))), _, (xs : (Minic_ast.expr list))) = _menhir_stack in
            let _v =
              let v = 
# 229 "<standard.mly>"
    ( xs )
# 1405 "minic_parser.ml"
               in
              (
# 265 "minic_parser.mly"
                                                          ( optim(Call (f, v)))
# 1410 "minic_parser.ml"
               : (Minic_ast.expr))
            in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | END ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | SEMI ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((((_menhir_stack, _menhir_s), _, (t : (Minic_ast.typ))), (x : (
# 108 "minic_parser.mly"
       (string)
# 1437 "minic_parser.ml"
                ))), (n : (
# 106 "minic_parser.mly"
       (int)
# 1441 "minic_parser.ml"
                ))), _, (xs : (Minic_ast.expr list))) = _menhir_stack in
                let _v =
                  let le = 
# 229 "<standard.mly>"
    ( xs )
# 1447 "minic_parser.ml"
                   in
                  (
# 185 "minic_parser.mly"
( { identity=x; type_elements=t; length=n; content=le} )
# 1452 "minic_parser.ml"
                   : (Minic_ast.tab_def))
                in
                _menhir_goto_tab_decl _menhir_env _menhir_stack _menhir_s _v
            | BOOL | EOF | FLOAT | INT | STRING | TAB | VOID ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let (((((_menhir_stack, _menhir_s), _, _), _), _), _, (xs : (Minic_ast.expr list))) = _menhir_stack in
                let _v =
                  let _11 = 
# 229 "<standard.mly>"
    ( xs )
# 1463 "minic_parser.ml"
                   in
                  (
# 181 "minic_parser.mly"
( failwith "Missing semicolon after table declaration" )
# 1468 "minic_parser.ml"
                   : (Minic_ast.tab_def))
                in
                _menhir_goto_tab_decl _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_reduce21 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (
# 108 "minic_parser.mly"
       (string)
# 1490 "minic_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (x : (
# 108 "minic_parser.mly"
       (string)
# 1496 "minic_parser.ml"
    ))) = _menhir_stack in
    let _v : (Minic_ast.expr) = 
# 264 "minic_parser.mly"
          ( Get(x))
# 1501 "minic_parser.ml"
     in
    _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v

and _menhir_run22 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail * _menhir_state * (
# 108 "minic_parser.mly"
       (string)
# 1508 "minic_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState22 _v
    | RPAR ->
        _menhir_reduce45 _menhir_env (Obj.magic _menhir_stack) MenhirState22
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState22

and _menhir_goto_expression :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState16 | MenhirState54 | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | COMMA ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL_CST _v ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
            | CST _v ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
            | FCST _v ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
            | IDENT _v ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
            | LPAR ->
                _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState54
            | NOT ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState54
            | OPOS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState54
            | STR _v ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState54)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | END | RPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (x : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr list) = 
# 238 "<standard.mly>"
    ( [ x ] )
# 1601 "minic_parser.ml"
             in
            _menhir_goto_separated_nonempty_list_COMMA_expression_ _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | ADD | AND | BOOL | BOOL_CST _ | COMMA | CST _ | DIV | END | EOF | EQ | FCST _ | FLOAT | FOR | GT | GTEQ | IDENT _ | IF | INT | LPAR | LT | LTEQ | MUL | NOT | OPOS | OR | POW | PUTCHAR | RETURN | RPAR | SEMI | STR _ | STRING | TAB | VOID | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Minic_ast.expr))), _, (e2 : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr) = 
# 267 "minic_parser.mly"
                                     ( Pow(e1,e2))
# 1623 "minic_parser.ml"
             in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (e1 : (Minic_ast.expr))), _, (e2 : (Minic_ast.expr))) = _menhir_stack in
        let _v : (Minic_ast.expr) = 
# 268 "minic_parser.mly"
                                      (Concat(e1,e2))
# 1639 "minic_parser.ml"
         in
        _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | AND | BOOL | BOOL_CST _ | COMMA | CST _ | END | EOF | EQ | FCST _ | FLOAT | FOR | GT | GTEQ | IDENT _ | IF | INT | LPAR | LT | LTEQ | NOT | OPOS | OR | PUTCHAR | RETURN | RPAR | SEMI | STR _ | STRING | TAB | VOID | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Minic_ast.expr))), _, (e2 : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr) = 
# 262 "minic_parser.mly"
                                     ( optim(Or(e1,e2)) )
# 1663 "minic_parser.ml"
             in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | ADD | AND | BOOL | BOOL_CST _ | COMMA | CST _ | DIV | END | EOF | EQ | FCST _ | FLOAT | FOR | GT | GTEQ | IDENT _ | IF | INT | LPAR | LT | LTEQ | MUL | NOT | OPOS | OR | PUTCHAR | RETURN | RPAR | SEMI | STR _ | STRING | TAB | VOID | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Minic_ast.expr))), _, (e2 : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr) = 
# 253 "minic_parser.mly"
                                      ( optim (Mul(e1,e2) ))
# 1687 "minic_parser.ml"
             in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | ADD | AND | BOOL | BOOL_CST _ | COMMA | CST _ | DIV | END | EOF | EQ | FCST _ | FLOAT | FOR | GT | GTEQ | IDENT _ | IF | INT | LPAR | LT | LTEQ | MUL | NOT | OPOS | OR | PUTCHAR | RETURN | RPAR | SEMI | STR _ | STRING | TAB | VOID | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Minic_ast.expr))), _, (e2 : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr) = 
# 254 "minic_parser.mly"
                                      ( optim (Div(e1,e2)) )
# 1711 "minic_parser.ml"
             in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | ADD | AND | BOOL | BOOL_CST _ | COMMA | CST _ | END | EOF | EQ | FCST _ | FLOAT | FOR | GT | GTEQ | IDENT _ | IF | INT | LPAR | LT | LTEQ | NOT | OPOS | OR | PUTCHAR | RETURN | RPAR | SEMI | STR _ | STRING | TAB | VOID | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Minic_ast.expr))), _, (e2 : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr) = 
# 252 "minic_parser.mly"
                                      ( optim(Add(e1,e2)) )
# 1739 "minic_parser.ml"
             in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | BOOL | BOOL_CST _ | COMMA | CST _ | END | EOF | FCST _ | FLOAT | FOR | GT | GTEQ | IDENT _ | IF | INT | LPAR | LT | LTEQ | NOT | OPOS | PUTCHAR | RETURN | RPAR | SEMI | STR _ | STRING | TAB | VOID | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Minic_ast.expr))), _, (e2 : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr) = 
# 256 "minic_parser.mly"
                                       (optim(LtEq(e1,e2)) )
# 1775 "minic_parser.ml"
             in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | BOOL | BOOL_CST _ | COMMA | CST _ | END | EOF | EQ | FCST _ | FLOAT | FOR | GT | GTEQ | IDENT _ | IF | INT | LPAR | LT | LTEQ | NOT | OPOS | PUTCHAR | RETURN | RPAR | SEMI | STR _ | STRING | TAB | VOID | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Minic_ast.expr))), _, (e2 : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr) = 
# 259 "minic_parser.mly"
                                     ( optim (Eq(e1,e2)) )
# 1809 "minic_parser.ml"
             in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | AND | BOOL | BOOL_CST _ | COMMA | CST _ | END | EOF | EQ | FCST _ | FLOAT | FOR | GT | GTEQ | IDENT _ | IF | INT | LPAR | LT | LTEQ | NOT | OPOS | OR | PUTCHAR | RETURN | RPAR | SEMI | STR _ | STRING | TAB | VOID | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Minic_ast.expr))), _, (e2 : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr) = 
# 263 "minic_parser.mly"
                                      ( optim(And(e1,e2) ))
# 1839 "minic_parser.ml"
             in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState48 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | BOOL | BOOL_CST _ | COMMA | CST _ | END | EOF | FCST _ | FLOAT | FOR | GT | IDENT _ | IF | INT | LPAR | LT | NOT | OPOS | PUTCHAR | RETURN | RPAR | SEMI | STR _ | STRING | TAB | VOID | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Minic_ast.expr))), _, (e2 : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr) = 
# 255 "minic_parser.mly"
                                     (optim (Lt(e1,e2)) )
# 1879 "minic_parser.ml"
             in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | BOOL | BOOL_CST _ | COMMA | CST _ | END | EOF | FCST _ | FLOAT | FOR | GT | GTEQ | IDENT _ | IF | INT | LPAR | LT | LTEQ | NOT | OPOS | PUTCHAR | RETURN | RPAR | SEMI | STR _ | STRING | TAB | VOID | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Minic_ast.expr))), _, (e2 : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr) = 
# 258 "minic_parser.mly"
                                       ( optim (GtEq(e1,e2)) )
# 1915 "minic_parser.ml"
             in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | BOOL | BOOL_CST _ | COMMA | CST _ | END | EOF | FCST _ | FLOAT | FOR | GT | IDENT _ | IF | INT | LPAR | LT | NOT | OPOS | PUTCHAR | RETURN | RPAR | SEMI | STR _ | STRING | TAB | VOID | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (e1 : (Minic_ast.expr))), _, (e2 : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr) = 
# 257 "minic_parser.mly"
                                     ( optim (Gt(e1,e2)) )
# 1955 "minic_parser.ml"
             in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | RPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.expr) = 
# 266 "minic_parser.mly"
                           (optim( Epar(e) ))
# 2001 "minic_parser.ml"
             in
            _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, (e : (Minic_ast.expr))) = _menhir_stack in
        let _v : (Minic_ast.expr) = 
# 261 "minic_parser.mly"
                     ( optim (Not(e)))
# 2017 "minic_parser.ml"
         in
        _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s), _, (e : (Minic_ast.expr))) = _menhir_stack in
        let _v : (Minic_ast.expr) = 
# 260 "minic_parser.mly"
                      (optim ( Opos(e)) )
# 2027 "minic_parser.ml"
         in
        _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v
    | MenhirState67 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (t : (Minic_ast.typ))), (x : (
# 108 "minic_parser.mly"
       (string)
# 2066 "minic_parser.ml"
            ))), _, (e : (Minic_ast.expr))) = _menhir_stack in
            let _v : (string * Minic_ast.typ * Minic_ast.expr) = 
# 176 "minic_parser.mly"
                                      ( (x, t, e) )
# 2071 "minic_parser.ml"
             in
            _menhir_goto_variable_decl _menhir_env _menhir_stack _menhir_s _v
        | BOOL | BOOL_CST _ | CST _ | END | EOF | FCST _ | FLOAT | FOR | IDENT _ | IF | INT | LPAR | NOT | OPOS | PUTCHAR | RETURN | STR _ | STRING | TAB | VOID | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, _), _), _, _) = _menhir_stack in
            let _v : (string * Minic_ast.typ * Minic_ast.expr) = 
# 174 "minic_parser.mly"
                           ( failwith "Missing semicolon after variable declaration" )
# 2080 "minic_parser.ml"
             in
            _menhir_goto_variable_decl _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState74 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | COMMA | RPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (((_menhir_stack, _menhir_s, (t : (Minic_ast.typ))), (x : (
# 108 "minic_parser.mly"
       (string)
# 2123 "minic_parser.ml"
            ))), _, (e : (Minic_ast.expr))) = _menhir_stack in
            let _v : (string * Minic_ast.typ * Minic_ast.expr) = 
# 192 "minic_parser.mly"
                                 ( (x, t, e) )
# 2128 "minic_parser.ml"
             in
            _menhir_goto_param_decl _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | RPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BEGIN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BOOL_CST _v ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
                | CST _v ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
                | FCST _v ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
                | FOR ->
                    _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState92
                | IDENT _v ->
                    _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
                | IF ->
                    _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState92
                | LPAR ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState92
                | NOT ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState92
                | OPOS ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState92
                | PUTCHAR ->
                    _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState92
                | RETURN ->
                    _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState92
                | STR _v ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState92 _v
                | WHILE ->
                    _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState92
                | END ->
                    _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState92
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState92)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, (e : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.instr) = 
# 228 "minic_parser.mly"
                           ( Return(e) )
# 2257 "minic_parser.ml"
             in
            _menhir_goto_instruction _menhir_env _menhir_stack _menhir_s _v
        | BOOL_CST _ | CST _ | END | FCST _ | FOR | IDENT _ | IF | LPAR | NOT | OPOS | PUTCHAR | RETURN | STR _ | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s), _, _) = _menhir_stack in
            let _v : (Minic_ast.instr) = 
# 224 "minic_parser.mly"
                    ( failwith "Missing semicolon after 'return'" )
# 2266 "minic_parser.ml"
             in
            _menhir_goto_instruction _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState97 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | RPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | SEMI ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, (e : (Minic_ast.expr))) = _menhir_stack in
                let _v : (Minic_ast.instr) = 
# 229 "minic_parser.mly"
                                      ( Putchar(e) )
# 2317 "minic_parser.ml"
                 in
                _menhir_goto_instruction _menhir_env _menhir_stack _menhir_s _v
            | BOOL_CST _ | CST _ | END | FCST _ | FOR | IDENT _ | IF | LPAR | NOT | OPOS | PUTCHAR | RETURN | STR _ | WHILE ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s), _, _) = _menhir_stack in
                let _v : (Minic_ast.instr) = 
# 225 "minic_parser.mly"
                               ( failwith "Missing semicolon after 'putchar'" )
# 2326 "minic_parser.ml"
                 in
                _menhir_goto_instruction _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState102 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | RPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BEGIN ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BOOL_CST _v ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
                | CST _v ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
                | FCST _v ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
                | FOR ->
                    _menhir_run113 _menhir_env (Obj.magic _menhir_stack) MenhirState105
                | IDENT _v ->
                    _menhir_run106 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
                | IF ->
                    _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState105
                | LPAR ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState105
                | NOT ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState105
                | OPOS ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState105
                | PUTCHAR ->
                    _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState105
                | RETURN ->
                    _menhir_run93 _menhir_env (Obj.magic _menhir_stack) MenhirState105
                | STR _v ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
                | WHILE ->
                    _menhir_run88 _menhir_env (Obj.magic _menhir_stack) MenhirState105
                | END ->
                    _menhir_reduce41 _menhir_env (Obj.magic _menhir_stack) MenhirState105
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState105)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (x : (
# 108 "minic_parser.mly"
       (string)
# 2460 "minic_parser.ml"
            ))), _, (e : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.instr) = 
# 233 "minic_parser.mly"
                                  ( Set(x,e))
# 2465 "minic_parser.ml"
             in
            _menhir_goto_instruction _menhir_env _menhir_stack _menhir_s _v
        | BOOL_CST _ | CST _ | END | FCST _ | FOR | IDENT _ | IF | LPAR | NOT | OPOS | PUTCHAR | RETURN | STR _ | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _, _) = _menhir_stack in
            let _v : (Minic_ast.instr) = 
# 226 "minic_parser.mly"
                       ( failwith "Missing semicolon after value assignment '='" )
# 2474 "minic_parser.ml"
             in
            _menhir_goto_instruction _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState110 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (x : (
# 108 "minic_parser.mly"
       (string)
# 2519 "minic_parser.ml"
            ))), _, (e : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.instr) = 
# 234 "minic_parser.mly"
                                       ( AddSet(x,e) )
# 2524 "minic_parser.ml"
             in
            _menhir_goto_instruction _menhir_env _menhir_stack _menhir_s _v
        | BOOL_CST _ | CST _ | END | FCST _ | FOR | IDENT _ | IF | LPAR | NOT | OPOS | PUTCHAR | RETURN | STR _ | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, _), _, _) = _menhir_stack in
            let _v : (Minic_ast.instr) = 
# 227 "minic_parser.mly"
                          ( failwith "Missing semicolon after value assignment '+='" )
# 2533 "minic_parser.ml"
             in
            _menhir_goto_instruction _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | RPAR | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (x : (
# 108 "minic_parser.mly"
       (string)
# 2576 "minic_parser.ml"
            ))), _, (e : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.instr) = 
# 239 "minic_parser.mly"
                             ( Set(x,e))
# 2581 "minic_parser.ml"
             in
            _menhir_goto_instruction_for _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | RPAR | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let ((_menhir_stack, _menhir_s, (x : (
# 108 "minic_parser.mly"
       (string)
# 2624 "minic_parser.ml"
            ))), _, (e : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.instr) = 
# 240 "minic_parser.mly"
                                  ( AddSet(x,e) )
# 2629 "minic_parser.ml"
             in
            _menhir_goto_instruction_for _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState121 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | SEMI ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT _v ->
                _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState123)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState87 | MenhirState92 | MenhirState105 | MenhirState135 | MenhirState126 | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | ADD ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack)
        | AND ->
            _menhir_run46 _menhir_env (Obj.magic _menhir_stack)
        | CONC ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack)
        | DIV ->
            _menhir_run38 _menhir_env (Obj.magic _menhir_stack)
        | EQ ->
            _menhir_run44 _menhir_env (Obj.magic _menhir_stack)
        | GT ->
            _menhir_run52 _menhir_env (Obj.magic _menhir_stack)
        | GTEQ ->
            _menhir_run50 _menhir_env (Obj.magic _menhir_stack)
        | LT ->
            _menhir_run48 _menhir_env (Obj.magic _menhir_stack)
        | LTEQ ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack)
        | MUL ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack)
        | OR ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack)
        | POW ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack)
        | BOOL_CST _ | CST _ | END | FCST _ | FOR | IDENT _ | IF | LPAR | NOT | OPOS | PUTCHAR | RETURN | STR _ | WHILE ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (e : (Minic_ast.expr))) = _menhir_stack in
            let _v : (Minic_ast.instr) = 
# 235 "minic_parser.mly"
                 ( Expr(e) )
# 2719 "minic_parser.ml"
             in
            _menhir_goto_instruction _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_fail :  'a. unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_param_decl :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (string * Minic_ast.typ * Minic_ast.expr) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | FLOAT ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | INT ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | STRING ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78)
    | RPAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, (x : (string * Minic_ast.typ * Minic_ast.expr))) = _menhir_stack in
        let _v : ((string * Minic_ast.typ * Minic_ast.expr) list) = 
# 238 "<standard.mly>"
    ( [ x ] )
# 2768 "minic_parser.ml"
         in
        _menhir_goto_separated_nonempty_list_COMMA_param_decl_ _menhir_env _menhir_stack _menhir_s _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce67 :  'ttv_tail 'ttv_return. _menhir_env -> ('ttv_tail * _menhir_state * (Minic_ast.typ)) * (
# 108 "minic_parser.mly"
       (string)
# 2781 "minic_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
    let _v : (string * Minic_ast.typ * Minic_ast.expr) = 
# 175 "minic_parser.mly"
            ( failwith "Missing semicolon after variable declaration" )
# 2788 "minic_parser.ml"
     in
    _menhir_goto_variable_decl _menhir_env _menhir_stack _menhir_s _v

and _menhir_run67 :  'ttv_tail 'ttv_return. _menhir_env -> ('ttv_tail * _menhir_state * (Minic_ast.typ)) * (
# 108 "minic_parser.mly"
       (string)
# 2795 "minic_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState67
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState67
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState67
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState67

and _menhir_run70 :  'ttv_tail 'ttv_return. _menhir_env -> ('ttv_tail * _menhir_state * (Minic_ast.typ)) * (
# 108 "minic_parser.mly"
       (string)
# 2825 "minic_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let ((_menhir_stack, _menhir_s, (t : (Minic_ast.typ))), (x : (
# 108 "minic_parser.mly"
       (string)
# 2833 "minic_parser.ml"
    ))) = _menhir_stack in
    let _v : (string * Minic_ast.typ * Minic_ast.expr) = 
# 177 "minic_parser.mly"
                     ( (x, t, Empty) )
# 2838 "minic_parser.ml"
     in
    _menhir_goto_variable_decl _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_loption_separated_nonempty_list_COMMA_param_decl__ :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * Minic_ast.typ * Minic_ast.expr) list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BEGIN ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | BOOL ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | FLOAT ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | INT ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | STRING ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | VOID ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | BOOL_CST _ | CST _ | END | FCST _ | FOR | IDENT _ | IF | LPAR | NOT | OPOS | PUTCHAR | RETURN | STR _ | WHILE ->
                _menhir_reduce43 _menhir_env (Obj.magic _menhir_stack) MenhirState82
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_reduce45 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : (Minic_ast.expr list) = 
# 139 "<standard.mly>"
    ( [] )
# 2893 "minic_parser.ml"
     in
    _menhir_goto_loption_separated_nonempty_list_COMMA_expression__ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run17 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 108 "minic_parser.mly"
       (string)
# 2900 "minic_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (s : (
# 108 "minic_parser.mly"
       (string)
# 2908 "minic_parser.ml"
    )) = _v in
    let _v : (Minic_ast.expr) = 
# 250 "minic_parser.mly"
          (SCst(s))
# 2913 "minic_parser.ml"
     in
    _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v

and _menhir_run18 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18

and _menhir_run19 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState19
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState19 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState19

and _menhir_run20 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL_CST _v ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | CST _v ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | FCST _v ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | IDENT _v ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | LPAR ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | NOT ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | OPOS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | STR _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20

and _menhir_run21 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 108 "minic_parser.mly"
       (string)
# 3001 "minic_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAR ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack)
    | ADD | AND | BOOL | BOOL_CST _ | COMMA | CONC | CST _ | DIV | END | EOF | EQ | FCST _ | FLOAT | FOR | GT | GTEQ | IDENT _ | IF | INT | LT | LTEQ | MUL | NOT | OPOS | OR | POW | PUTCHAR | RETURN | RPAR | SEMI | STR _ | STRING | TAB | VOID | WHILE ->
        _menhir_reduce21 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run23 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 109 "minic_parser.mly"
       (float)
# 3022 "minic_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (f : (
# 109 "minic_parser.mly"
       (float)
# 3030 "minic_parser.ml"
    )) = _v in
    let _v : (Minic_ast.expr) = 
# 251 "minic_parser.mly"
          (FCst(f))
# 3035 "minic_parser.ml"
     in
    _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v

and _menhir_run24 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 106 "minic_parser.mly"
       (int)
# 3042 "minic_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (n : (
# 106 "minic_parser.mly"
       (int)
# 3050 "minic_parser.ml"
    )) = _v in
    let _v : (Minic_ast.expr) = 
# 248 "minic_parser.mly"
        ( Cst(n) )
# 3055 "minic_parser.ml"
     in
    _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v

and _menhir_run25 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 107 "minic_parser.mly"
       (bool)
# 3062 "minic_parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (b : (
# 107 "minic_parser.mly"
       (bool)
# 3070 "minic_parser.ml"
    )) = _v in
    let _v : (Minic_ast.expr) = 
# 249 "minic_parser.mly"
             ( BCst(b) )
# 3075 "minic_parser.ml"
     in
    _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_tab_decl :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (Minic_ast.tab_def) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_stack = Obj.magic _menhir_stack in
    assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState142
    | FLOAT ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState142
    | INT ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState142
    | STRING ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState142
    | TAB ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState142
    | VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState142
    | EOF ->
        _menhir_reduce1 _menhir_env (Obj.magic _menhir_stack) MenhirState142
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState142

and _menhir_goto_program :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (Minic_ast.prog) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = Obj.magic _menhir_stack in
    let _menhir_stack = Obj.magic _menhir_stack in
    let (_1 : (Minic_ast.prog)) = _v in
    Obj.magic _1

and _menhir_goto_declaration_list :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> ((string * Minic_ast.typ * Minic_ast.expr) list * Minic_ast.tab_def list *
  Minic_ast.fun_def list) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (fd : (Minic_ast.fun_def))), _, (dl : ((string * Minic_ast.typ * Minic_ast.expr) list * Minic_ast.tab_def list *
  Minic_ast.fun_def list))) = _menhir_stack in
        let _v : ((string * Minic_ast.typ * Minic_ast.expr) list * Minic_ast.tab_def list *
  Minic_ast.fun_def list) = 
# 164 "minic_parser.mly"
                                       ( let vl, tl, fl = dl in
                                         vl, tl, fd :: fl )
# 3127 "minic_parser.ml"
         in
        _menhir_goto_declaration_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (td : (Minic_ast.tab_def))), _, (dl : ((string * Minic_ast.typ * Minic_ast.expr) list * Minic_ast.tab_def list *
  Minic_ast.fun_def list))) = _menhir_stack in
        let _v : ((string * Minic_ast.typ * Minic_ast.expr) list * Minic_ast.tab_def list *
  Minic_ast.fun_def list) = 
# 162 "minic_parser.mly"
                                  ( let vl, tl, fl = dl in
                                         vl, td :: tl, fl )
# 3140 "minic_parser.ml"
         in
        _menhir_goto_declaration_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, (vd : (string * Minic_ast.typ * Minic_ast.expr))), _, (dl : ((string * Minic_ast.typ * Minic_ast.expr) list * Minic_ast.tab_def list *
  Minic_ast.fun_def list))) = _menhir_stack in
        let _v : ((string * Minic_ast.typ * Minic_ast.expr) list * Minic_ast.tab_def list *
  Minic_ast.fun_def list) = 
# 160 "minic_parser.mly"
                                       ( let vl, tl, fl = dl in
                                         vd :: vl, tl, fl )
# 3153 "minic_parser.ml"
         in
        _menhir_goto_declaration_list _menhir_env _menhir_stack _menhir_s _v
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | EOF ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, (dl : ((string * Minic_ast.typ * Minic_ast.expr) list * Minic_ast.tab_def list *
  Minic_ast.fun_def list))) = _menhir_stack in
            let _v : (Minic_ast.prog) = 
# 146 "minic_parser.mly"
       ( let var_list, tab_list, fun_list = dl in
         { globals = var_list; tables = tab_list; functions = fun_list; } )
# 3170 "minic_parser.ml"
             in
            _menhir_goto_program _menhir_env _menhir_stack _menhir_s _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_goto_typ :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> (Minic_ast.typ) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | RPAR ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | IDENT _v ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | LBRACKET ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    (match _tok with
                    | CST _v ->
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let _menhir_stack = (_menhir_stack, _v) in
                        let _menhir_env = _menhir_discard _menhir_env in
                        let _tok = _menhir_env._menhir_token in
                        (match _tok with
                        | RBRACKET ->
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let _menhir_env = _menhir_discard _menhir_env in
                            let _tok = _menhir_env._menhir_token in
                            (match _tok with
                            | SEMI ->
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let _menhir_env = _menhir_discard _menhir_env in
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let ((((_menhir_stack, _menhir_s), _, (t : (Minic_ast.typ))), (x : (
# 108 "minic_parser.mly"
       (string)
# 3225 "minic_parser.ml"
                                ))), (n : (
# 106 "minic_parser.mly"
       (int)
# 3229 "minic_parser.ml"
                                ))) = _menhir_stack in
                                let _v : (Minic_ast.tab_def) = 
# 187 "minic_parser.mly"
( { identity=x; type_elements=t; length=n; content=[]} )
# 3234 "minic_parser.ml"
                                 in
                                _menhir_goto_tab_decl _menhir_env _menhir_stack _menhir_s _v
                            | SET ->
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let _menhir_env = _menhir_discard _menhir_env in
                                let _tok = _menhir_env._menhir_token in
                                (match _tok with
                                | BEGIN ->
                                    let _menhir_stack = Obj.magic _menhir_stack in
                                    let _menhir_env = _menhir_discard _menhir_env in
                                    let _tok = _menhir_env._menhir_token in
                                    (match _tok with
                                    | BOOL_CST _v ->
                                        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
                                    | CST _v ->
                                        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
                                    | FCST _v ->
                                        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
                                    | IDENT _v ->
                                        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
                                    | LPAR ->
                                        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                                    | NOT ->
                                        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                                    | OPOS ->
                                        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                                    | STR _v ->
                                        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
                                    | END ->
                                        _menhir_reduce45 _menhir_env (Obj.magic _menhir_stack) MenhirState16
                                    | _ ->
                                        assert (not _menhir_env._menhir_error);
                                        _menhir_env._menhir_error <- true;
                                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16)
                                | _ ->
                                    assert (not _menhir_env._menhir_error);
                                    _menhir_env._menhir_error <- true;
                                    let _menhir_stack = Obj.magic _menhir_stack in
                                    let (((_menhir_stack, _menhir_s, _), _), _) = _menhir_stack in
                                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                            | BOOL | EOF | FLOAT | INT | STRING | TAB | VOID ->
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let ((((_menhir_stack, _menhir_s), _, _), _), _) = _menhir_stack in
                                let _v : (Minic_ast.tab_def) = 
# 183 "minic_parser.mly"
( failwith "Missing semicolon after table declaration" )
# 3281 "minic_parser.ml"
                                 in
                                _menhir_goto_tab_decl _menhir_env _menhir_stack _menhir_s _v
                            | _ ->
                                assert (not _menhir_env._menhir_error);
                                _menhir_env._menhir_error <- true;
                                let _menhir_stack = Obj.magic _menhir_stack in
                                let (((_menhir_stack, _menhir_s, _), _), _) = _menhir_stack in
                                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                        | _ ->
                            assert (not _menhir_env._menhir_error);
                            _menhir_env._menhir_error <- true;
                            let _menhir_stack = Obj.magic _menhir_stack in
                            let (((_menhir_stack, _menhir_s, _), _), _) = _menhir_stack in
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        let _menhir_stack = Obj.magic _menhir_stack in
                        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState0 | MenhirState143 | MenhirState142 | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | LPAR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BOOL ->
                    _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState71
                | FLOAT ->
                    _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState71
                | INT ->
                    _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState71
                | STRING ->
                    _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState71
                | VOID ->
                    _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState71
                | RPAR ->
                    let _menhir_stack = Obj.magic _menhir_stack in
                    let _menhir_s = MenhirState71 in
                    let _v : ((string * Minic_ast.typ * Minic_ast.expr) list) = 
# 139 "<standard.mly>"
    ( [] )
# 3352 "minic_parser.ml"
                     in
                    _menhir_goto_loption_separated_nonempty_list_COMMA_param_decl__ _menhir_env _menhir_stack _menhir_s _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState71)
            | SEMI ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack)
            | SET ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
            | BOOL | EOF | FLOAT | INT | STRING | TAB | VOID ->
                _menhir_reduce67 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState78 | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | SET ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                (match _tok with
                | BOOL_CST _v ->
                    _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
                | CST _v ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
                | FCST _v ->
                    _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
                | IDENT _v ->
                    _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
                | LPAR ->
                    _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState74
                | NOT ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState74
                | OPOS ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState74
                | STR _v ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState74)
            | COMMA | RPAR ->
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, (t : (Minic_ast.typ))), (x : (
# 108 "minic_parser.mly"
       (string)
# 3418 "minic_parser.ml"
                ))) = _menhir_stack in
                let _v : (string * Minic_ast.typ * Minic_ast.expr) = 
# 193 "minic_parser.mly"
                ( (x, t, Empty) )
# 3423 "minic_parser.ml"
                 in
                _menhir_goto_param_decl _menhir_env _menhir_stack _menhir_s _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | MenhirState82 | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | IDENT _v ->
            let _menhir_stack = Obj.magic _menhir_stack in
            let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            (match _tok with
            | SEMI ->
                _menhir_run70 _menhir_env (Obj.magic _menhir_stack)
            | SET ->
                _menhir_run67 _menhir_env (Obj.magic _menhir_stack)
            | BOOL | BOOL_CST _ | CST _ | END | FCST _ | FLOAT | FOR | IDENT _ | IF | INT | LPAR | NOT | OPOS | PUTCHAR | RETURN | STR _ | STRING | VOID | WHILE ->
                _menhir_reduce67 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let _menhir_stack = Obj.magic _menhir_stack in
                let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let _menhir_stack = Obj.magic _menhir_stack in
            let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
    | _ ->
        _menhir_fail ()

and _menhir_errorcase :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState143 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState142 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState135 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState129 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState126 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState123 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState121 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState118 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState116 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState114 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState110 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState107 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState105 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState102 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState97 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState93 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState92 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState89 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState87 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState83 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState82 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState78 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState74 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState71 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState67 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState64 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState54 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState52 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState50 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState48 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState46 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState44 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState42 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState40 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState38 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState36 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState34 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState32 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState30 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState22 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState20 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState19 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState18 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState16 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (((_menhir_stack, _menhir_s, _), _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState4 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
    | MenhirState0 ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_s = MenhirState0 in
        let _startpos = _menhir_env._menhir_lexbuf.Lexing.lex_start_p in
        let _menhir_stack = Obj.magic _menhir_stack in
        let _startpos__1_ = _startpos in
        let _v =
          let _startpos = _startpos__1_ in
          (
# 148 "minic_parser.mly"
        ( let pos = _startpos in
          let message =
            Printf.sprintf
              "Syntax error at %d, %d"
              pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
          in
          failwith message )
# 3671 "minic_parser.ml"
           : (Minic_ast.prog))
        in
        _menhir_goto_program _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce1 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : ((string * Minic_ast.typ * Minic_ast.expr) list * Minic_ast.tab_def list *
  Minic_ast.fun_def list) = 
# 159 "minic_parser.mly"
             ( [], [], [] )
# 3682 "minic_parser.ml"
     in
    _menhir_goto_declaration_list _menhir_env _menhir_stack _menhir_s _v

and _menhir_run2 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (Minic_ast.typ) = 
# 203 "minic_parser.mly"
       (Void)
# 3693 "minic_parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run3 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAR ->
        let _menhir_stack = Obj.magic _menhir_stack in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        (match _tok with
        | BOOL ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | FLOAT ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | INT ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | STRING ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState4
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState4)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let _menhir_stack = Obj.magic _menhir_stack in
        let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s

and _menhir_run5 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (Minic_ast.typ) = 
# 204 "minic_parser.mly"
         (String)
# 3736 "minic_parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run6 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (Minic_ast.typ) = 
# 201 "minic_parser.mly"
      ( Int )
# 3747 "minic_parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run7 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (Minic_ast.typ) = 
# 205 "minic_parser.mly"
        (Float)
# 3758 "minic_parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run8 :  'ttv_tail 'ttv_return. _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _menhir_stack = Obj.magic _menhir_stack in
    let _v : (Minic_ast.typ) = 
# 202 "minic_parser.mly"
       ( Bool )
# 3769 "minic_parser.ml"
     in
    _menhir_goto_typ _menhir_env _menhir_stack _menhir_s _v

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and program : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Minic_ast.prog) =
  fun lexer lexbuf ->
    let _menhir_env = {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = Obj.magic ();
      _menhir_error = false;
    } in
    Obj.magic (let _menhir_stack = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | BOOL ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | FLOAT ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | INT ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | STRING ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | TAB ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | EOF ->
        _menhir_reduce1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)
