(* TD While_suite
Vu la compléxité, on a travaillé à plusieurs

MALOD Victor
BLANQUET Antoine
GONZALEZ Jules
LANQUETIN Alexis

alexis.lanquetin@etu.univ-grenoble-alpes.fr

On continue le TP de la dernière fois. On cherche toujours
à analyser des programmes comme

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

Travail à effectuer :
- Si pas fait lors de la séance précédente:
  écrire en ocaml un type d'AST pour les programmes visés et
  fonction de type : string -> ast qui rend l'AST correspondant
  si la string fait partie du langage défini par cette grammaire.
- Écrivez une autre version de vos fonctions qui utilisent des combinateurs,
  comme cela est fait dans
    https://ltpf.gricad-pages.univ-grenoble-alpes.fr/PF/anacomb.ml
- Écrivez une autre version de anacomb.ml (anacomblazy.ml), qui utilise
  des listes paresseuses
- Écrivez une autre version de vos fonctions qui utilisent les listes paresseuses
- facultatif (pas pour les paresseux donc):
  Écrivez une autre version de vos fonctions qui utilisent le type
  Stream.t (https://caml.inria.fr/pub/docs/manual-ocaml/libref/Stream.html)

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
let (+>) (a : 'r analist) (b : ('r, 't) st) : ('r, 't) st =
  fun l -> let l = a l in b l

(* a rendant un résultat suivi de b, ce dernier pouvant rendre un résultat *)
let (++>) (a : ('r, 't) ranalist) (b : 'x -> ('r, 't) st) : ('r, 't) st =
  fun l -> let (x, l) = a l in b x l

(* Choix entre a ou b *)
let (+|) (a : ('r, 't) st) (b : ('r, 't) st) : ('r, 't) st =
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

let terminal_var: (var,char) ranalist = fun l -> match l with
  | x :: l ->  (return (assoc_var x) l)
  | _ -> raise Echec

let assoc_cons c: cons = match c with
  | '0' -> O
  | '1' -> I
  | _ -> raise Echec;;

let terminal_cons : (cons,char) ranalist = fun l -> match l with
  | x :: l ->  (return (assoc_cons x) l)
  | _ -> raise Echec

let p_V : (var, char) ranalist =
  fun l ->  terminal_var l


let p_C : (cons, char) ranalist =
  fun l -> terminal_cons l


let p_E : (exp, char) ranalist =
  fun l -> try
          let e,l = p_V l in (V(e), l)
        with Echec ->  let e, l = p_C l in (C(e),l)


let rec p_S : ('r, 't) ranalist =
  fun l -> try
          let x1,l = p_I l in
          let x2,l = p_L l in
          (Seq(x1,x2),l)
        with Echec -> (Skip, l)
and p_L : ('r, 't) ranalist =
  fun l -> try let l = terminal ';' l in  p_S l with Echec -> (Skip, l)
and p_I : ('r, 't) ranalist =
  fun l -> try let v,l = p_V l in
               let l = terminal ':' l in
               let l = terminal '=' l in
               let e, l = p_E l in Assign(v,e),l with Echec ->
                                                     try let l = terminal 'i' l in
                                                         let l = terminal '.' l in
                                                         let e,l = p_E l in
                                                         let l = terminal '{' l in
                                                         let seqT,l = p_S l in
                                                         let l = terminal '}' l in
                                                         let l = terminal '{' l in
                                                         let seqF,l = p_S l in
                                                         let l = terminal '}' l in
                                                         If(e, seqT, seqF),l with Echec ->
                                                                                  try let l = terminal 'w' l in
                                                                                  let l = terminal '.' l in
                                                                                  let e,l = p_E l in
                                                                                  let l = terminal '{' l in
                                                                                  let seq,l = p_S l in
                                                                                  let l = terminal '}' l in
                                                                                  While(e,seq),l with Echec -> (Skip,l)
                                                       
                               

let prog = list_of_string  "a:=1;b:=1;c:=1;w.a{i.c{c:=0;a:=b}{b:=0;c:=a}}";;
p_S prog;;
