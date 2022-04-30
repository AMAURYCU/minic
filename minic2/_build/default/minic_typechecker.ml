open Minic_ast
(* Pour représenter les environnements associant chaque variable à son type. *)
module Env = Map.Make(String)
(* Vérification du bon typage d'un programme. *)
let typecheck_program (prog: prog) =
  (* L'environnement global mémorise le type de chaque variable globale. *)
  
  let global_env =
    List.fold_left (fun env (x, ty, _) -> Env.add x ty env) Env.empty prog.globals
  in
  
  (* Vérification du bon typage d'une fonction.
     C'est une fonction locale : on a accès à [prog] et à [global_env]. *)
  let typecheck_function (fdef: fun_def) =
    
    (* On devrait ici avoir également un environnement local.
       À COMPLÉTER
     *)
    let local_env =
      List.fold_left (fun env (x, ty, _) -> Env.add x ty env) Env.empty fdef.locals
    in

    let param_env = 
      List.fold_left (fun env (x, ty, _) -> Env.add x ty env) Env.empty fdef.params
    in
    (* Vérification du bon typage et calcul du type d'une expression.
       À nouveau, fonction locale avec accès à tout ce qui est au-dessus. *)
    let rec type_expr = function
      | Cst _ -> Int
      | BCst _ -> Bool
      |SCst _ -> String
      | Empty -> Void
      |FCst _ -> Float
      | Add(e1,e2) -> let te1 = type_expr e1 in
                      let te2 = type_expr e2 in
                      if (te1<>Int && te1<> Float) || (te2<> Int && te2 <> Float)
                      then failwith "expr type error"
                      else if te1 ==Float ||te2 == Float then Float else Int
      | Mul(e1,e2) -> let te1 = type_expr e1 in
                      let te2 = type_expr e2 in
                      if (te1<>Int && te1<> Float) || (te2<> Int && te2 <> Float)
                      then failwith "expr type error"
                      else if te1 ==Float ||te2 == Float then Float else Int
      | Div(e1,e2) -> let te1 = type_expr e1 in
                      let te2 = type_expr e2 in
                      if (te1<>Int && te1<> Float) || (te2<> Int && te2 <> Float)
                      then failwith "expr type error"
                      else if te1 ==Float ||te2 == Float then Float else Int
      | Lt(e1,e2) ->  let te1 = type_expr e1 in let te2 = type_expr e2 in
                      if (te1 <> Int && te1 <> Float) || (te2 <> Int && te2<>Float)
                      then failwith "expr type error"
                      else Bool
      | LtEq(e1,e2) ->  let te1 = type_expr e1 in let te2 = type_expr e2 in
                      if (te1 <> Int && te1 <> Float) || (te2 <> Int && te2<>Float)
                      then failwith "expr type error"
                      else Bool
      | Gt(e1,e2) ->  let te1 = type_expr e1 in let te2 = type_expr e2 in
                      if (te1 <> Int && te1 <> Float) || (te2 <> Int && te2<>Float)
                      then failwith "expr type error"
                      else Bool
      | GtEq(e1,e2) -> let te1 = type_expr e1 in let te2 = type_expr e2 in
                      if (te1 <> Int && te1 <> Float) || (te2 <> Int && te2<>Float)
                      then failwith "expr type error"
                      else Bool
      | Eq(e1,e2) ->  let te1 = type_expr e1 in let te2 = type_expr e2 in
                      if (te1 <> Int && te1 <> Float) || (te2 <> Int && te2<>Float)
                      then failwith "expr type error"
                      else Bool
      | Opos(e) -> let te = type_expr e in
                  if te <> Int && te <> Float
                  then failwith "expr type error"
                  else te
      | Not(e) -> let te = type_expr e in
                  if te <> Bool
                  then failwith "expr type error"
                  else Bool
      | And(e1,e2) -> let te1 = type_expr e1 in
                      let te2 = type_expr e2 in
                      if (te1 <> Bool) || (te2 <> Bool)
                      then failwith "expr type error"
                      else Bool
      | Or(e1,e2) ->  let te1 = type_expr e1 in
                      let te2 = type_expr e2 in
                      if (te1 <> Bool) || (te2 <> Bool)
                      then failwith "expr type error"
                      else Bool
      | Get(x) -> let tx =
                  begin
                    try Env.find x global_env (* on recherche le type de x dans les variables globales*)
                    with Not_found -> try Env.find x param_env(* on recherche le type de x dans les variables locales*)
                    with Not_found -> try Env.find x local_env (* on recherche le type de x dans les parametres*)
                    with Not_found -> failwith "Get : Variable never declared"
                  end
                  in tx
      | Call(f, v) -> let tf =
                      begin
                        let fct = List.find (fun g -> f = g.name) (prog.functions) in
                        let comparison = (List.compare_lengths v (fct.params)) in
                          if comparison <> 0
                          then
                            begin
                              if comparison > 0 then failwith "Call: Too many arguments"; 
                              if comparison < 0 then failwith "Call: Arguments missing"
                            end
                          else List.iter2 (fun pf pfct -> if type_expr pf <> (let get2nd (_,t,_) = t in get2nd pfct) then failwith "Call : type error") v (fct.params); fct.return
                      end
                      in tf
      | Epar(e) -> let te = type_expr e
                   in te 
      | EComma(e) -> let te = type_expr e
                   in te 
      | Pow(e1,e2) -> let ep = type_expr e1 in let esec = type_expr e2 in if (ep <> Int&& ep<> Float) || esec <> Int then failwith"Pow: Type error" else ep
      | Concat(e1,e2) -> let ep = type_expr e1 in let esec = type_expr e2 in if ep<> String ||esec <> String then failwith"Concat: Type error not string" else String
    in
    (* Vérification du bon typage d'une instruction ou d'une séquence.
       Toujours local. *)
    let rec typecheck_instr = function
      (* Cas d'une instruction [return]. On vérifie que le type correspond au
         type de retour attendu par la fonction dans laquelle on se trouve. *)
      | Return(e) -> let t = type_expr e in
                     if t <> fdef.return
                     then failwith "Return: type error"
      | Putchar(e) -> let t = type_expr e in 
                      if t <> Int
                      then failwith "Putchar: type error" (*NEW*)
      | If(c, s1, s2) -> let tc = type_expr c in
                      if tc <> Bool
                      then failwith "If : condition type error" (*NEW - à compléter*)
                      else let test1 typecheck_seq s1 = let _ = typecheck_seq s1 in () in
                          (try test1 typecheck_seq s1
                          with Failure "expr type error" -> failwith "If : seq 1 type error");
                          let test2 typecheck_seq s2 = let _ = typecheck_seq s2 in () in
                          (try test2 typecheck_seq s2
                          with Failure "expr type error" -> failwith "If : seq 2 type error")
      | While(c, s) -> let tc = type_expr c in
                      if tc <> Bool
                      then failwith "While : condition type error" (*NEW*)
                      else let test typecheck_seq s = let _ = typecheck_seq s in () in
                      (try test typecheck_seq s
                      with Failure "expr type error" -> failwith "While : seq type error")
      | Set(x,e) -> let te = type_expr e in
                    let tx =
                    begin
                      try Env.find x global_env (* on recherche le type de x dans les variables globales*)
                      with Not_found -> try Env.find x param_env (* on recherche le type de x dans les variables locales*)
                      with Not_found -> try Env.find x local_env(* on recherche le type de x dans les parametres*)
                      with Not_found -> failwith "Set : Variable never declared"
                    end
                    in
                    if tx <> te
                    then failwith "Set : type error" (*NEW*)
      | AddSet(x,e) -> let te = type_expr e in
                    let tx =
                    begin
                      try Env.find x global_env (* on recherche le type de x dans les variables globales*)
                      with Not_found -> try Env.find x param_env (* on recherche le type de x dans les variables locales*)
                      with Not_found -> try Env.find x local_env(* on recherche le type de x dans les parametres*)
                      with Not_found -> failwith "AddSet : Variable never declared"
                    end
                    in
                    if (te <> Int) || (tx <> Int )
                    then failwith "AddSet : type error" (*NEW*)
      | Expr(e) ->  let test type_expr e = let _ = type_expr e in () in
                    (try test type_expr e
                    with Failure "expr type error" -> failwith "Expr : type error")
      | For(init, cond, incr, s) -> let tcond = type_expr cond in
                                    if tcond <> Bool
                                    then failwith "For : condition type error" (*NEW*)
                                    else 
                                    begin
                                      let test_s typecheck_seq s = let _ = typecheck_seq s in () in
                                      (try test_s typecheck_seq s
                                      with Failure "expr type error" -> failwith "While : seq type error");
                                      let test_init typecheck_instr init = let _ = typecheck_instr init in () in
                                      (try test_init typecheck_instr init
                                      with Failure "expr type error" -> failwith "While : seq type error");
                                      let test_incr typecheck_instr incr = let _ = typecheck_instr incr in () in
                                      (try test_incr typecheck_instr incr
                                      with Failure "expr type error" -> failwith "While : seq type error")
                                    end
                   
    and typecheck_seq s =
      List.iter typecheck_instr s        
    in

    (* On vérifie les valeurs initiales des variables globales et locales*)
    let typecheck_var (_, t, e) =
    begin
      if e <> Empty
      then let te = type_expr e in
      begin
        if t <> te
        then  failwith "Global : type error"
      end
    end
    in
    let typecheck_tab (tdef: tab_def) =
    begin
      let tcont = List.length (tdef.content) in
      if tcont <> 0
      then
        begin
            if tcont <> (tdef.length)
            then failwith "Tab : table size error"
            else
            List.iter (fun e -> if (type_expr e) <> (tdef.type_elements) then failwith "Tab : type error") tdef.content
        end
    end
    in
    List.iter typecheck_tab (prog.tables);
    List.iter typecheck_var (prog.globals);
    List.iter typecheck_var (fdef.locals);

    (* Code principal du typage d'une fonction : on type ses instructions. *)
    typecheck_seq (fdef.code);
  in

  (* Code principal du typage d'un programme : on type ses fonctions.
   *)
  if List.length (prog.functions) = 0
  then failwith "Prog: No function in code, please add at least one function declaration"
  else List.iter typecheck_function (prog.functions);