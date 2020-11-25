(* 
a:=1;
b:=1;
c:=1;
w(a){
 i(c){
  c:=0;
  a:=b
 }{
  b:=0;
  c:=a
 }
}

à l'aide d'une grammaire (définissant le langage while):

V pour variable1
C pour constante
E pour expression
I pour instruction

S pour axiome (tradition dans les grammaires)
L pour liste d'instructions

  S ::= IL | ε
  L ::= ;S | ε
  I ::= V:=E | i.E{S}{S} | w.E{S} | ε


 *)

exception Echec

let list_of_string s =
  let rec boucle s i n =
    if i = n then [] else s.[i] :: boucle s (i+1) n
  in boucle s 0 (String.length s)


type var = A | B | C | D
type cons = O | I
type exp = V of var | C of cons
type ins = Seq of ins * ins | Assign of var * exp | While of exp * ins | If of exp * ins * ins | Skip

type ('r,'t) ranalist = 't list -> 'r * 't list

type ('r,'t) st = 't list -> 'r

type 't analist = 't list -> 't list


(* a suivi de b, ce dernier pouvant rendre un résultat *)
let (+>) (a : 'r analist) b =
  fun l -> let l = a l in b l

(* a rendant un résultat suivi de b, ce dernier pouvant rendre un résultat *)
let (++>) (a : ('r, 't) ranalist) b =
  fun l -> let (x, l) = a l in b x l

(* Choix entre a ou b *)
let (+|) (a : ('r, 't) st) (b : ('r, 't) st) =
  fun l -> try a l with Echec -> b l

(* *)
let return : 'r -> ('r, 't) ranalist =
  fun x l -> (x, l)


let terminal c : 't analist = fun l -> match l with
  | x :: l when x = c ->  l
  | _ -> raise Echec

let assoc_var c: var = match c with
  | 'a' -> A
  | 'b' -> B
  | 'c' -> C
  | 'd' -> D
  | _ -> raise Echec;;

let terminal_var c : ('r, 't) ranalist = fun l -> match l with
  | x :: l -> ((assoc_var x), l)
  | _ -> raise Echec


let p_V : (var, char) ranalist =
  fun l -> (terminal_var 'a' +| terminal_var 'b' +| terminal_var 'c' +| terminal_var 'd') l



let assoc_cons c: cons = match c with
  | '0' -> O
  | '1' -> I
  | _ -> raise Echec;;

let terminal_cons c : ('r, 't) ranalist = fun l -> match l with
  | x :: l -> ((assoc_cons x), l)
  | _ -> raise Echec


let p_C : (cons, char) ranalist =
  fun l -> (terminal_cons '0' +| terminal_cons '1') l


let prog = list_of_string "a";;
p_V prog;;

let p_E : (exp, char) ranalist =
  fun l -> ((p_V ++> fun v -> return (V(v)))
            +| (p_C ++> fun c -> return (C(c)))) l

let prog = list_of_string "a";;
p_E prog;;

let p_P : char analist =
  fun l -> terminal ';' l


let rec p_S : ('r, 't) ranalist =
  fun l -> (p_I ++> fun i -> (p_L ++> fun s -> return (Seq(i,s)))) l
and p_L : ('r, 't) ranalist =
  fun l ->  ((p_P +> p_S) +| (return Skip)) l

and p_I : ('r, 't) ranalist =
  fun l -> ((p_V ++> (fun v -> (terminal ':' +> (terminal '=' +> p_E)) ++> fun e -> return (Assign(v,e)) ))
                             +| ((terminal 'i' +> (terminal '.' +> p_E)) ++>
                                   (fun e -> ((terminal '{' +> p_S) ++>
                                     (fun seq1 -> (terminal '}' +> (terminal '{' +> p_S) ++>
                                                     (fun seq2 -> (terminal '}' +> return (If(e, seq1, seq2)))))))))                                                  +| ((terminal 'w' +> (terminal '.' +> p_E) ++>
                                                                                                                                                                             (fun w -> (terminal '{' +> p_S ++>
                                                                                                                                                                                          (fun seq -> (terminal '}' +> return (While(w, seq))))))))) l
        


let prog = list_of_string  "a:=1;b:=1;c:=1;w.a{i.c{c:=0;a:=b}{b:=0;c:=a}}";;

p_S prog;;

