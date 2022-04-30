   let rec optim = function
|Add(e1, e2) ->
let ep = optim e1 in
let esec = optim e2 in
begin match ep, esec with
| Cst n1, Cst n2 -> Cst (n1 + n2)
| _, _ -> Add(ep, esec)
end
|Mul(e1,e2) ->let ep = optim e1 in
let esec = optim e2 in
begin match ep, esec with
| Cst n1, Cst n2 -> Cst (n1 * n2)
| _, _ -> Mul(ep, esec)
end 
|Div(e1,e2) -> let ep = optim e1 in
let esec = optim e2 in
begin match ep, esec with
| Cst n1, Cst n2 -> Cst (n1 / n2)
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
            