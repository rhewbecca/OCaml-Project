type ide = string;;
type exp = 
	| Eint of int 
	| Ebool of bool 
        | Estring of string
	| Den of ide 
	| Prod of exp * exp 
	| Sum of exp * exp 
	| Diff of exp * exp 
	| Eq of exp * exp 
	| Minus of exp 
	| IsZero of exp 
	| Or of exp * exp 
	| And of exp * exp 
	| Not of exp 
	| Ifthenelse of exp * exp * exp 
	| Let of ide * exp * exp 
	| Fun of ide * exp 
	| FunCall of exp * exp 
	| Letrec of ide * exp * exp
        | EDict of edictionary (*definisce un dizionario*)
        | Get of exp * ide (*richiede un elemento all'interno di un dizionario*)
        | Remove of exp * ide (*rimuove un elemento all'interno di un dizionario*)
        | Add of exp * ide * exp (*aggiunge un nuovo elemento nel dizionario*)
        | Clear of exp (*rimuove tutti gli elementi di un dizionario*)
        | ApplyOver of exp * exp (*applica una funzione a tutti gli elementi presenti in un dizionario*)

and edictionary= Eempty| EItem of ide*exp*edictionary

;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT =
	| Int of int 
	| Bool of bool 
	| String of string (*identifica le stringhe*)
        | Unbound 
	| FunVal of evFun 
	| RecFunVal of ide * evFun
        | Dict of dicti (*identifica un dizionario*)
and evFun = ide * exp * evT env
and dicti = Empty| Item of ide*evT*dicti (*il dizionario può essere Empty (vuoto) oppure formato dalla tripla descritta*)

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
                "int" -> (match v with
		Int(_) -> true 
		| _ -> false) 
		| "bool" -> (match v with
		Bool(_) -> true 
		| _ -> false)
		(*controlla che il parametro v sia una stringa*)
                | "string" -> (match v with
                String(_) -> true 
                | _ -> false)
		(*controlla che il parametro v sia un dizionario*)
                | "dictionary" ->( match v with 
                Dict(_) -> true
                | _ -> false)
		| _ -> failwith("not a valid type");;
                

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		| Bool(true) -> Bool(false) 
		| Bool(false) -> Bool(true))
	else failwith("Type error");;

(*cerca un elemento nel dizionario e ritorna il valore ad esso associato*)
let rec get (d) (key:ide) :evT =
        match d with
           Empty -> Unbound
           | Item(i,item,xs) -> if i=key then item
            else get xs key;;

(*cerca una chiave nel dizionario e ne rimuove il valore ad esso associato*)
let rec rm (d) (key:ide) =
        match d with
            Empty -> Empty
          | Item(i,item,xs) -> if i=key then xs
            else Item(i,item,(rm xs key));;

(*aggiunge un elemento nel dizionario (se non è già presente) oppure aggiorna il valore ad esso associato*)
let rec add (d) (key:ide) (v: evT) =
           match d with
               Empty -> Item(key,v,Empty)
             | Item(i,item,xs) -> if i=key then Item(i,v,xs)
               else Item(i,item,(add xs key v));;

(*elimina tutti gli elementi presenti nel dizionario*)
let clear d= Empty;;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	| Eint n -> Int n 
	| Ebool b -> Bool b 
	| Estring s -> String s
        | IsZero a -> iszero (eval a r) 
	| Den i -> applyenv r i 
	| Eq(a, b) -> eq (eval a r) (eval b r) 
	| Prod(a, b) -> prod (eval a r) (eval b r) 
	| Sum(a, b) -> sum (eval a r) (eval b r) 
	| Diff(a, b) -> diff (eval a r) (eval b r) 
	| Minus a -> minus (eval a r) 
	| And(a, b) -> et (eval a r) (eval b r) 
	| Or(a, b) -> vel (eval a r) (eval b r) 
	| Not a -> non (eval a r) 
	| Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") 
	| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) 
	| Fun(i, a) -> FunVal(i, a, r) 
	| FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) 
	                    | RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv 
	                     | _ -> failwith("non functional value")) 
	| Letrec(f, funDef, letBody) -> (match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1
	                              | _ -> failwith("non functional def"))
        
	(*tramite l’uso di una funzione ausiliaria evalDict, essa valuta ricorsivamente le espressioni presenti nel dizionario e restituisce lo stesso con le espressioni valutate*)
        | EDict d -> let rec evalDict (dict:edictionary) (env : evT env):dicti =( 
                                         match dict with
                                            Eempty -> Empty
                                          | EItem(i,item,xs) -> Item(i, (eval item env),(evalDict xs env))) in
                     Dict(evalDict d r)
	(*viene controllato che il parametro d sia un dizionario, se lo è restituisce il valore associato alla chiave considerata, altrimenti lancia un errore di tipo*)
        | Get (d,key) -> let dictionary = (eval d r) in
            if(typecheck "dictionary" dictionary ) then let Dict(list)=dictionary in get list key
            else failwith("Type error")
	(*viene controllato che il parametro d sia un dizionario, se lo è rimuove la chiave considerata dal dizionario, altrimenti lancia un errore di tipo*)
        | Remove (d,key) -> let dictionary = (eval d r) in
            if(typecheck "dictionary" dictionary ) then let Dict(list)=dictionary in Dict(rm list key)
            else failwith("Type error")
	(*controlla e valuta value e d, in seguito a esito positivo aggiunge il valore scelto al dizionario, altrimenti lancia un errore di tipo*)
        | Add (d,key,value) -> let dictionary = (eval d r) in
          let valuted = (eval value r) in
            if(typecheck "dictionary" dictionary) then let Dict(list)=dictionary in Dict( add list key valuted)
            else failwith("Type error")
	(*viene controllato che il parametro d sia un dizionario, se lo è elimina tutti gli elementi presenti nel dizionario*)
        | Clear d -> let dictionary = (eval d r) in
            if (typecheck"dictionary" dictionary) then let Dict(list)=dictionary in Dict(clear list)
            else failwith("Type error")
	(*controlla e valuta i parametri d e f, in seguito a esito positivo applica la funzione f ad ogni elemento presente nel dizionario d e restituisce il nuovo dizionario aggiornato*)
        | ApplyOver(f,d) -> let dictionary=(eval d r) in
          let funClosure =(eval f r) in 
          let rec apply dict func=
             (match dict with
             Empty->Empty
            |Item(i,item,xs) ->(match func with
				FunVal(arg, fBody, fDecEnv) -> 
					Item(i,(eval fBody (bind fDecEnv arg item)),(apply xs func)) 
	                        | RecFunVal(g, (arg, fBody, fDecEnv)) -> 
						let rEnv = (bind fDecEnv g func) in
							let aEnv = (bind rEnv arg item) in
								Item(i,(eval fBody aEnv),(apply xs func)) 
	                     | _ -> failwith("non functional value"))) in
          if (typecheck"dictionary" dictionary) then let Dict(list)=dictionary in Dict(apply list funClosure)
          else failwith("Type error")
;;
		
(* =============================  TESTS  ================= *)

let env0 = emptyenv Unbound;; (*Ambiente vuoto*)

let d1=EDict(EItem("ABQ",Eint(1),EItem("BRI",Eint(2),EItem("PER",Eint(13),Eempty))));; (*dizionario di tre elementi*)

eval d1 env0;; (*definizione del dizionario*)

eval (Get(d1, "BCN")) env0;; (*Get cerca di ottenere il valore associato alla chiave BCN e restituisce Unbound poiché nessun valore è associato alla chiave BCN*)

eval (Get(d1,"BRI")) env0;; (*Get ottiene il valore associato alla chiave BRI*)

eval (Add(d1, "BRI", Eint(3659))) env0;; (*Add aggiunge alla chiave BRI il valore scelto*)

eval (Add(d1, "PER", Diff(Eint(20),Eint(10)))) env0;; (*Add aggiunge alla chiave PER il risultato della differenza*)

eval (Remove(d1, "ABQ")) env0;; (*Remove rimuove il valore associato alla chiave ABQ*)

eval (Remove(d1, "LDE")) env0;; (*Remove rimuove il valore associato alla chiave LDE, ma poiché non è presente il dizionario rimane invariato*)

eval (Clear(d1)) env0;; (*Clear rimuove tutti i valori associati alle chiavi presenti nel dizionario*)

eval (Clear(Estring("Aeroporti"))) env0;; (*Clear cerca di rimuovere su un valore che non è un dizionario, quindi lancia un'eccezione di tipo*)

let f1= Fun("Prodotto", Prod(Den "Prodotto",Eint(2)));; (*Funzione che raddoppia il suo argomento*)

let f2= Fun("Negativo", Minus(Den "Negativo"));; (*Funzione che rende un elemento negativo*)

let f3= Fun("Azzerato", IsZero(Den "Azzerato"));; (*Funzione che controlla se un elemento è uguale a 0*)

eval (ApplyOver(f1,d1)) env0;; (*Applica la funzione f1 a tutti gli elementi del dizionario d1*)

eval (ApplyOver(f2,d1)) env0;; (*Applica la funzione f2 a tutti gli elementi del dizionario d1*)

eval (ApplyOver(f3,d1)) env0;; (*Applica la funzione f3 a tutti gli elementi del dizionario d1*)

let f4= Fun("Decremento", ApplyOver(Fun("y",Diff(Den "y", Eint(1))), Den "Decremento"));; (*Funzione ApplyOver che esegue un decremento su un argomento y*)

let f5= Fun("Aggiungere", Add(Den "Aggiungere", "LPL",Eint(010)));; (*Funzione che aggiunge la chiave LPL al dizionario passato come argomento*)

let d2=EDict(EItem("dizionario1",d1,EItem("dizionario2",EDict(Eempty),Eempty)));; (*dizionario che contiene due dizionari come elementi*)

eval (ApplyOver(f4,d2)) env0;; (*ApplyOver di f4 sul dizionario d2*)

eval (ApplyOver(f5,d2)) env0;; (*ApplyOver di f5 sul dizionario d2*)
