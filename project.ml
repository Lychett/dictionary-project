(* nei commenti presenti nel programma uso chiave ed etichetta come sinonimi *)
type ide = string;;

type exp = (*tipi di dato*)
	| Eint of int 
	| Estring of string
	| Ebool of bool 
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
	| FunBinary of ide * ide * exp          (* coppia di parametri formali, corpo *)
	| FunCallBinary of exp * exp * exp 
	| Letrec of ide * ide * exp * exp       (* nomefun, parametro, corpo, bodylet *)
	| Dict of (ide * exp) list              (* definisco il dizionario come una lista di coppie identificatore espressione *)
	| Insert_Dict of exp * ide * exp        (* dizionario, chiave, valore *)
	| Delete_Dict of exp * ide              (* dizionario, chiave *)
	| Has_key_Dict of exp * ide             (* dizionario, chiave *)
	| Iterate_Dict of exp * exp             (* funzione (unaria), dizionario *)
	| Fold_Dict of exp * exp                (* funzione (binaria), dizionario *)
	| Filter_Dict of exp * (ide list);;     (* dizionario , lista di chiavi *)

(* ambiente polimorfo *)
type 't env = (string * 't) list;;          (* contiene valori *)

let emptyenv (x : 't) = [("",x)];;

let rec applyenv ((r : 't env), (i : ide)) = match r with
	| [(_,e)] -> e
	| (i1,e1)::xs -> if i=i1 then e1 else applyenv (xs,i)
	| [] -> failwith ("not present in this amb");;

let bind (r : 't env) (i : ide) (v : 't) = (i,v)::r;;

(* tipi esprimibili *)
type evT = 
	| Int of int 
	| String of string
	| Bool of bool 
	| Unbound 
	| FunVal of evFun 
	| RecFunVal of ide * evFun      (* nomefun,par,corpo,ambiente dove è stata dichiarata *)
	| FunValBinary of evFunBinary
	| DictVal of (ide * evT) list   (* valore esprimibile per un dizionario *)
and evFunBinary = ide * ide * exp * evT env
and evFun = ide * exp * evT env;;

(* controllo dei tipi per descrittore*)
let typecheck (s : string) (v : evT) : bool = match s with
	| "int" -> (match v with
			| Int(_) -> true 
			| _ -> false)
	| "string" -> (match v with
			| String(_) -> true 
			| _ -> false)
	| "bool" -> (match v with
			|Bool(_) -> true 
			| _ -> false) 
	| _ -> failwith("not a valid type");;

(* funzioni primitive *)
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

(* alcune funzioni ausiliarie per il dizionario *)

(* dict: dizionario, label: chiave. Restituisce l'elemento associato alla chiave *)
let rec lookupdict dict label =
	match dict with
		| [] -> failwith("chiave non trovata nel dizionario")
		| (x,y)::xs -> if (label = x) then y 
		               else lookupdict xs label;;

(* dict: dizionario, label: chiave. Restituisce T se la chiave e' presente nel dizionario, F altrimenti *)
let rec member dict label : bool =
	match dict with
		| [] -> false
		| (x,y)::xs -> if (label = x) then true else member xs label;;
		
    
let typeof (a : evT) : string =
    if (typecheck "int" a)=true then "int"
    else if (typecheck "string" a)=true then "string"
         else if (typecheck "bool" a)=true then "bool"
              else failwith ("non e' un tipo considerato primitivo");;
		
let same_type (x : evT) (y : evT) : bool =
    if ((typeof x) == (typeof y)) then true
    else false;;

(* rimuove i duplicati dal dizionario, usata solo alla creazione del dizionario per verificare che non stia creando un dizionario
   che contiene 2 chiavi uguali, rimuove la prima occorrenza del doppione, in generale lascia solo l'ultima occorrenza *)
let rec removeDup dict =
	match dict with
		| [] -> []
		| (x,y)::xs -> if (member xs x) then removeDup xs else (x,y)::removeDup xs;;
		
(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	| Eint n -> Int n 
	| Estring s -> String s
	| Ebool b -> Bool b 
	| IsZero a -> iszero (eval a r) 
	| Den i -> applyenv (r,i) 
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
				else failwith ("non-boolean guard") 
	| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) 
	| Fun(i, a) -> FunVal(i, a, r)                              (* il valore di una funzione è una chiusura *) 
	| FunBinary(ar1, ar2, a) -> FunValBinary(ar1, ar2, a, r)
	| FunCall(f, eArg) -> (*scoping statico*)
		let fClosure = (eval f r) in
			(match fClosure with
				| FunVal(arg, fBody, fDecEnv) -> 
				    let aVal = eval eArg r in
					    let aEnv = bind fDecEnv arg aVal in
					        eval fBody aEnv
				| RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in                 (* valuto il parametro attuale nell'ambiente del chiamante *)
						let rEnv = (bind fDecEnv g fClosure) in (* nuovo ambiente esteso con il binding tra il nome della funzione (g) e la sua chiusura ricorsiva *)
							let aEnv = (bind rEnv arg aVal) in  (* nuovo ambiente contenente la chiusura ricorsiva esteso con il binding tra il                                         parametro formale e l'ambiente dove è valutato il parametro attuale *)
								eval fBody aEnv                 (* valuto il body del let nell'ultimo ambiente calcolato *)
				| _ -> failwith("non functional value")) 
	| FunCallBinary(f, eArg1, eArg2) ->
	    let fBinClosure = eval f r in
	        (match fBinClosure with
	            | FunValBinary(arg1, arg2, fBody, fDecEnv) ->
	                let aVal1 = eval eArg1 r in
	                    let aVal2 = eval eArg2 r in
	                        let aEnv1 = bind fDecEnv arg1 aVal1 in
	                            let aEnv2 = bind aEnv1 arg2 aVal2 in
	                                eval fBody aEnv2
	           | _ -> failwith("non functional value with pars"))				
	| Letrec(f, i, fBody, letBody) ->
        		let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in eval letBody r1 
    (* primo passo rimuovo le possibile coppie che hanno chiave gia' presente nel dizionario *)
	| Dict(dict) ->  let thisdict = removeDup dict in 
	                    let s=" " in
	                        DictVal(evalDict thisdict s r) 
	(* aggiunta ad un dizionario: prende un dizionario, una etichetta ed un espressione *)
    | Insert_Dict(thisdict,lab,valx) ->
		(match (eval thisdict r) with
			| DictVal(mydict) -> DictVal(insInDict mydict lab valx r)
			| _ -> failwith("wrong value"))
    (* rimozione di un elemento dal dizionario *)
	| Delete_Dict(thisdict,lab) ->
		(match (eval thisdict r) with
			| DictVal(mydict) -> DictVal(delFromDict mydict lab)
			| _ -> failwith("wrong value"))
	(* controlla che sia presente la chiave lab nel dizionario*)
   	| Has_key_Dict(thisdict, lab) -> 
     		(match (eval thisdict r) with
           		| DictVal(d) -> Bool(member d lab)
            		| _ -> failwith("wrong value"))
    (* applichiamo la funzione funx a tutti i valori del dizionario *)
	| Iterate_Dict(funx,thisdict) ->
		(match (eval thisdict r) with
			| DictVal(mydict) ->let fVal = eval funx r in DictVal(applyFunDict mydict fVal r)
			| _ -> failwith("wrong value"))

	| Fold_Dict(funx,thisdict) -> setForFold funx thisdict r
	
	| Filter_Dict(thisdict, key) ->
        (match (eval thisdict r) with
            (* in modff metto la lista di chiavi *)
            | DictVal(mydict) -> let modff = key in DictVal(fltrDict mydict key modff)
            | _ -> failwith("Errore di tipo, non e' un dizionaro"))
    
	and evalDict (dict : (ide*exp) list) (s : string) (r : evT env) = 
		(match dict with 
			| [] -> []
			| (x,y)::xs -> if (s = " ") (* se sono al primo elem del dizionario, allora lo inserisco ed s diventa il tipo dei valori del dizionario*)
					       then let nt = typeof(eval y r) in 
					            (x, eval y r) :: evalDict xs nt r
					       else let nt = typeof(eval y r) in 
					            if (nt = s)
					            then  (x, eval y r) :: evalDict xs nt r
					            else failwith("stai creando un diizionario con valori eterogenei, non puoi"))
					
	and insInDict (dict : (ide * evT) list) (lab : ide) (valx : exp) (r : evT env) =
	            (match dict with
	                | [] -> dict@[(lab,eval valx r)]
		        	| (x,y)::xs -> if (member dict lab)=true 
		        	               then failwith("chiave già presente") 
			                       else let v = eval valx r in
			                            if (same_type v y) then dict@[(lab,v)]
			                            else failwith("errore, stai ceracando di aggiungere un valore associato ad una chiave con tipo esprimibile diverso da quelli contenuti nel dizionario"))
					
	and delFromDict (dict : (ide * evT) list) (lab : ide) = 
				(match dict with
					| [] -> []
					| (x,y)::xs -> if (lab = x) then (delFromDict xs lab) else (x,y)::(delFromDict xs lab))
					
	and applyFunDict (dict : (ide * evT) list) (f : evT) (r : evT env) =
				(match dict with
					| [] -> []
					| (x,y)::xs ->  (x, (dictFunCall f y r))::(applyFunDict xs f r))
					
	and dictFunCall (f : evT) (y : evT) (r : evT env) =
				(match f with
					| FunVal(arg, fBody, fDecEnv) -> 
						let aEnv = bind fDecEnv arg y in
							    eval fBody aEnv
					| RecFunVal(g, (arg, fBody, fDecEnv)) ->  (* non valuto il parametro attuale nell'ambiente del chiamante perchè già un evT *)
						let rEnv = (bind fDecEnv g f) in 
						    let aEnv = (bind rEnv arg y) in 
							    eval fBody aEnv 
					| _ -> failwith("non functional value"))
						
	and setForFold (funx : exp) (dict : exp) (r : evT env)= 
	    (match (eval dict r) with 
	        | DictVal(mydict) -> 
	            (match mydict with 
    	            | [] -> failwith("stai applicando la fold ad un dizionario vuoto")
    	            | (x,y)::xs -> (match typeof(y) with
    	                           | ("string") -> let fVal = eval funx r in 
    	                                            let z=Estring "" in
    	                                                applyFunBinaryDict mydict fVal (eval z r) r
    	                           | ("int") -> let fVal = eval funx r in
    	                                            let w=Eint 0 in 
    	                                                applyFunBinaryDict mydict fVal (eval w r) r
    	                           | ("bool") -> let fVal = eval funx r in
    	                                            let b=Ebool false in
    	                                                applyFunBinaryDict mydict fVal (eval b r) r
    	                           | _ -> failwith("errore di tipo")))
    	   	| _ -> failwith("non e' un dizionario"))

	and applyFunBinaryDict (dict : (ide * evT) list) (f : evT) (acc : evT) (r : evT env) =
	            (match dict with
	                | [] -> acc
	                | (x,y)::xs -> applyFunBinaryDict xs f (dictFunBinaryCall f acc y r) r)  (* h::t -> fold f t (f acc h) *)
	                
	and dictFunBinaryCall (f : evT) (acc : evT) (y : evT) (r : evT env) =
	           (match f with 
	                   | FunValBinary(arg1, arg2, fBody, fDecEnv) ->
	                       let aEnv1 = bind fDecEnv arg1 acc in
	                            let aEnv2 = bind aEnv1 arg2 y in
	                                eval fBody aEnv2
	                   | _ -> failwith("non functional value"))  
	                   
	and fltrDict (dict : (ide * evT) list) (ilst : ide list) (modff : ide list) : ((ide * evT) list) =
                (match modff,dict with
                     _,[] -> []
                    | [], (id,vl)::restDict -> fltrDict (delFromDict dict id) ilst ilst
                    | x::xs, (id,vl)::restDict -> if x=id then (id,vl)::(fltrDict restDict ilst xs) (* xs perche non ho altre x: una volta che ne ho trovata una allora non ne ho piu' *)
                                                  else fltrDict dict ilst xs);;
				

(* ============================= * test interprete base * ============================= *)

(* definisco ambiente vuoto*)
let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 1)), Eint 3);;

eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;

eval e2 env0;;

let e3 = Letrec("fact","n",Ifthenelse(Eq(Den("n"),Eint(0)),Eint(1),Prod(Den("n"),FunCall(Den("fact"),Diff(Den("n"),Eint(1))))),FunCall(Den("fact"),Eint(3)));;

eval e3 env0;;

(* ============================= * test dizionario * ============================= *)

let magazzinoVuoto = Dict([]);;

eval magazzinoVuoto env0;;

(* prova: creazione di un dizionario che contiene funzioni che restituiscono tipi diversi *)
let magFun = Dict([("res1", FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3));("res2", FunCall(Fun("y",Or(Den "y", Ebool false)), Ebool true))]);;

(* stai creando un dizionario con valori eterogenei *)
eval magFun env0;;

(* prova: creazione di un dizionario valutabile *)
let magFun2 = Dict([("res1", Sum(Eint 1, Eint 3));("res2", Prod(Eint 3, Eint 6))]);;

eval magFun2 env0;;

(* prova creazione del dizionario con tipi esprimibili diversi, non devo avere la possibilita' di farlo *)
let magazzinoErrore = Dict([("marco", Eint 1);("matteo", Eint 2);("romolo", Estring "giulietta")]);;

eval magazzinoErrore env0;; 

(* prova creazione dizionario con chiavi non univoche, rimuove la prima inserita *)
let magazzinoDoppieChiavi = Dict([("carne ovina", Eint 435);("carne suina", Eint 456);("carne ovina", Eint 567);("carne equina", Eint 310)]);;

eval magazzinoDoppieChiavi env0;;

let magazzino = Dict([("mele", Eint 430);("banane", Eint 312);("arance", Eint 525);("pere", Eint 217)]);;

eval magazzino env0;;

let magazzinoInsert = Insert_Dict(magazzino,"kiwi", Eint 300);;

eval magazzinoInsert env0;;

(* faccio una insert ma con un valore che ha tipo esprimibile diverso da quelli associati alle altre chiavi del dizionario *)
let magazzinoWrongInsert = Insert_Dict(magazzino,"palla", Estring "sbaglio");;

eval magazzinoWrongInsert env0;;

(* provo a creare un altro magazzino in cui la chiave banane e' gia' presente, viene sollevata una eccezione *)
let magazzinoDoppione = Insert_Dict(magazzino,"banane", Eint 200);;

eval magazzinoDoppione env0;;

let magazzinoDeleted = Delete_Dict(magazzinoInsert, "pere");;

eval magazzinoDeleted env0;;

(* test sulla has_key *)
let val_bool = Has_key_Dict(magazzinoInsert, "banane");;

eval val_bool env0;;

(* test sulla iterate *)
let funToDict = Iterate_Dict(Fun("x", Sum(Den "x", Eint 1)), magazzinoInsert);;

eval funToDict env0;;

(* test sulla filter *)
let magazzinoFiltred = Filter_Dict(magazzino, ["mele";"pere"]);;

eval magazzinoFiltred env0;;

(* test sulla fold *)
let risultatoSomma = Fold_Dict(FunBinary("acc", "x", Sum(Den "acc", Sum(Den "x", Eint 1))), magazzino);;

eval risultatoSomma env0;;

(* test sulla iterate con errore *)
let dizionarioWrong = Dict([("number1", Eint 22222);("number2", Eint 33333)]);;

eval dizionarioWrong env0;;

let typerr = Iterate_Dict(Fun("x", Or(Den "x", Eint 1)),dizionarioWrong);;

(* Eccezione: stai usando operandi con tipi sbagliati rispetto all'operazione che vuoi fare *)
eval typerr env0;;
