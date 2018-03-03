(*a symbol is either defined as a Symbol("string") or as predefined symbol constructors *)
type symbol = Symbol of string | Aditya | Goku | Vegeta | Zero | Succ | Prec | Plus | G | H | A | B;;

(*a variable is either defined as a Variable("string") or as predefined variable constructors *)
type variable = Variable of string | X | Y | Z;;

type term = V of variable | Node of symbol*(term list);;

(*Pair created for defining signature*)
type pair = Pair of symbol*int;;

(*signature is a list of pairs containing symbols and their arity*)
let signature = [Pair(Goku,1);Pair(Vegeta,-3);Pair(Aditya,2);Pair(Goku,3)];;

open List;;

(*a map function created to implement a funciton on all elements of a list*)
let rec map f l = match l with 
	[] -> []
	| a::c -> (f a)::(map f c);;
	
(*to check the if a is in list b , returns bool*)	
let rec contains a b = match b with
            c::d -> if c = a then true else contains a d
            | [] -> false;;

(*to check duplicate elements in list l1 , returns false if duplicate exits*)			
let rec check_in_list l1 l2 = match l1 with|
    Pair(a,e)::b -> if contains a l2=false then check_in_list b (a::l2) else false
  | [] -> true;;
  
(*checking if list l of Pair contains any pair with negative arity , returns false if negative arity exists*)  
let rec check_negative l = match l with 
	Pair(a,b)::d -> if b<0 then false else check_negative d
	| [] -> true;;
	
(*funciton to check the if a signature is valid or not*)	
let check_sig li = if ((check_negative li = true) && (check_in_list li [] = true)) then true else false;;
	
(*exception is a symbol is not in signature*)	
exception NotInSignature;;
	
(*given a signature l returns the arity of symbol e*)	
let rec find_arity e l = match l with
      Pair(a,b)::c -> if a =e then b else find_arity e c
| [] -> raise NotInSignature;;

(*to check if all elements of list l with signature s are wfterm or not*)
let rec all_wf h s l = match l with 
	a::b -> if h a s = true then all_wf h s b else false
	| [] -> true;;

(*returns length of list*)	
let rec length_list l = match l with 
	a::b -> 1+ length_list b
	| [] -> 0;;
	
(*returns true if a term is well formed*)	
 let rec wfterm t signat= match t with
        Node(a,b) -> if find_arity a signat = length_list b then all_wf wfterm signat b else false
        | V(y) -> true;;
		
(*returns the number of nodes and variables in a term *)		
 let rec size a b = match b with
        Node(e1,e2) -> fold_left size (a+1) e2
        | V(y) -> 1+a;;

(*returns the max element of list b when a=0*)		
let rec max a b = match b with 
		e::f -> if e>a then max e f else max a f
		| [] -> a;;

(*returns the height of a term t*)		
let rec ht t = match t with 
		Node(a,[]) -> 0
	| Node(a,b) -> 1+ (max 0 (map ht b))
	| V(y) -> 0;;
	
(*returns all the variables in term t when a=[]*)	
let rec vars a t = match t with
  V(y) -> if contains y a then a else y::a
  | Node(e1,e2) -> fold_left vars a e2;;
  
		
 let a = Node(Goku,[Node(Vegeta,[Node(Aditya,[]);V(X)]);Node(Aditya,[V(Y);V(Z);V(X);V(Variable("dalla"))])]);;
(*returns the domain of the sigma l *)
  let rec domain l = match l with
        (a,b)::c -> a::(domain c)
        | [] -> [];;
			
(*exception*)			
exception NotInDomain;;
		
(*returns the substituion for a in the sigma s*)		
 let rec second a s = match s with
        (c,b)::d -> if a=c then b else second a d
        | [] -> raise NotInDomain;;

(*type sigma which contains all the subsitutions as a list of term*term , identity is Sigma([])*)		
 type sigma = Sigma of (term*term)list | Composite of sigma*sigma;;
 
(*given a term t and sigma a performs the substitution on t *) 
 let rec subst_one a t = match t with 
	V(x) -> if contains (V(x)) (domain a) then second (V(x)) a else V(x)
	| Node(x,y) -> Node(x,map (subst_one a) y);;
	
(*given a sigma s and term t substitutes*)	
let rec subst s t = match s with 
	Sigma (a) -> subst_one a t
	| Composite (a,b) -> subst b (subst a t);;

(*exception if two terms are not unifiable*) 
exception NOT_UNIFIABLE;;

(*removes the unnecessary Sigma([]) and Composite for the mgu*)
let rec filter s = match s with
        Composite(Sigma([]),a) -> filter a
        | Composite(a,Sigma([])) -> filter a
        | Composite(Sigma([]),Sigma([])) -> Sigma([])
        | Composite(a,b) -> Composite(filter a,filter b)
        | Sigma(a) -> Sigma(a);;

(*mgu is passed as m and final returns the mgu for the case of (Node(a,b))and (Node(a,c)) *)		
let rec final m x l1 l2 = match (l1,l2) with 
	(a::b,c::d) -> final m (Composite(x,(m a c))) (map (subst (Composite(x,(m a c)))) b) (map (subst (Composite(x,(m a c)))) d)
	| ([],[]) -> x
	| ([],a) -> raise NOT_UNIFIABLE
	| (a,[]) -> raise NOT_UNIFIABLE;;
	
(*given two terms t and u returns the mgu of the terms*)
      let rec mgu t u = match (t,u) with
              (V(x),V(y)) -> if x=y then Sigma([]) else Sigma([(V(x),V(y))])
            | (V(x),Node(a,[])) -> Sigma([(V(x),Node(a,[]))])
            | (Node(a,[]),V(x)) -> Sigma([(V(x),Node(a,[]))])
            | (Node(a,[]),Node(b,[])) -> if a=b then Sigma([]) else raise NOT_UNIFIABLE
            | (Node(a,[]),Node(b,c)) -> raise NOT_UNIFIABLE
            | (Node(b,c),Node(a,[])) -> raise NOT_UNIFIABLE
            | (V(x),Node(a,b))->if contains (x) (vars ([]) (Node(a,b))) then raise NOT_UNIFIABLE else Sigma([(V(x),Node(a,b))])
            | (Node(a,b),Node(c,d)) -> if a!=c then raise NOT_UNIFIABLE else filter (final mgu (Sigma([])) b d)
        |        (Node(a,b),V(x))->if contains (x) (vars ([]) (Node(a,b))) then raise NOT_UNIFIABLE else Sigma([(V(x),Node(a,b))]);;

		
(*----------------------------------------------------Examples---------------------------------------------------------------*)		
(*defining signature *)		
let signature =[Pair(Goku,1);Pair(Vegeta,2);Pair(Zero,0);Pair(Prec,1);Pair(Succ,1);Pair(Plus,2);Pair(G,2);Pair(H,2);Pair(A,0);Pair(B,0)];;

let invalid_sig1 =[Pair(G,1);Pair(G,2);Pair(H,3)];; 

let invalid_sig2 =[Pair(G,1);Pair(A,2);Pair(H,-3)];;

let invalid_sig3 =[Pair(G,1);Pair(G,2);Pair(H,-3)];; 
 
(*Checking check_sig function for different signatures*) 
check_sig signature;;

check_sig invalid_sig1;;

check_sig invalid_sig2;;

check_sig invalid_sig3;;

(*Checking wfterm with respect to signature*)
let a = Node(G,[Node(A,[V(X)])]);;

wfterm a signature;;

let u = Node(G,[Node(A,[]);V(Y)]);;

wfterm u signature;;

(*defining terms p and r to check ht size and vars*)
let p = Node(Plus,[V(X);Node(Plus,[V(Y);Node(Zero,[])])]);;

ht p;;

size 0 p;;

vars [] p;;
 
let r = Node(Plus,[Node(Succ,[V(Z)]);p]);;

ht r;;

size 0 r;;
 
vars [] p;;  

(*-----Checking subst--------- *)
(*sig2 defined (X -> Z) and (Z -> X)*)	
let sig2 = Sigma([(V(Y),V(Z));(V(Z),V(X))]);;

(**sig1 defined X->Y*)
let sig1 = Sigma([(V(X),V(Y))]);;		

(*comp is the composite of two sigmas sig1 and sig2 , performing sig1 first and then sig2 (X -> Z) and (Z->X)*) 
let comp = Composite(sig1,sig2);;
   
(*Defining a term 'b' for testing*)   
let b = Node(Vegeta,[(Node(Vegeta,[V(Y);V(Z)]));Node(Goku,[V(X)])]);;

(*substituting using sig1 on b*)
let s1 = subst sig1 b;;

(*substituting using sig2 on s1*)
let s2 = subst sig2 s1;;

(*substituting using comp on b*)
let s3= subst comp b;;

(*checking if composite gives correct answer*)
s2=s3;;

(*----------------Checking MGU----------------*)

let ques1 = Node(G,[Node(H,[V(X);Node(A,[])]);Node(H,[Node(B,[]);V(X)])]);;		 

let ques2 = Node(G,[Node(H,[Node(B,[]);Node(A,[])]);Node(H,[V(X);V(Z)])]);;

(*finding mgu for ques1 and ques2*)
mgu ques1 ques2;;
		 
let ques21 = Node(G,[Node(H,[V(X);Node(A,[])]);V(Y)]);;

let ques22 = Node(G,[V(Y);Node(H,[Node(B,[]);V(X)])]);;

(*finding mgu for ques21 and ques22*)
mgu ques21 ques22;;

(* finding mgu for same terms*)
mgu ques1 ques1;;
