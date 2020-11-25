(*
*    ---- TP5: while ----    * 
 *    TEYSSIER Theo    *
 *   LANQUETIN Alexis  *
 *  PRAT-CAPILA Hugo   *
 *)

exception Echec
type analist = char list -> char list

let list_of_string s =
  let rec boucle s i n =
    if i = n then [] else s.[i] :: boucle s (i+1) n
  in boucle s 0 (String.length s)

(* a suivi de b *)
let (+>) (a : analist) (b : analist) : analist =
  fun l -> b (a l)

(* choix entre a ou b *)
let (+|) (a : analist) (b : analist) : analist =
  fun l -> try a l with Echec -> b l

(* Généralisation *)
let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

let eps : analist = fun l -> l

let p_V : analist =
  fun l -> (terminal 'a' +| terminal 'b' +| terminal 'c' +| terminal 'd') l

let p_C : analist =
  fun l -> (terminal '0' +| terminal '1') l

let p_E : analist =
  fun l -> (p_V +| p_C) l

let p_P : analist =
  fun l -> terminal ';' l


let rec p_S : analist =
  fun l -> (p_I +> p_L +| eps) l
and p_L : analist =
  fun l ->  (p_P +> p_S +| eps) l
and p_I : analist =
  fun l -> ((p_V +> terminal ':' +> terminal '=' +> p_E) +|
             (terminal 'i' +> terminal '.' +> p_E +> terminal '{' +> p_S +> terminal '}' +>
                terminal '{' +> p_S +> terminal '}') +|
             (terminal 'w' +> terminal '.' +> p_E +> terminal '{' +> p_S +> terminal '}') +|
             eps ) l

             

let isValid = fun s -> match p_S (list_of_string s) with
                              | [] -> true
                              | _ -> false;;


assert((isValid "a:=1") = true);;
assert((isValid "a==1") = false);;
assert((isValid "i.1{c:=0}{c:=1}") = true);;
assert((isValid "i.1{c:=0;c:=1}") = false);;
assert((isValid "w.1{c:=0}") = true);;
assert((isValid "w.1c:=0") = false);;
assert((isValid "a:=1;b:=1;c:=1;w.a{i.c{c:=0;a:=b}{b:=0;c:=a}}") = true);;


(*
############################
#         AST              #
############################
On a essayer mais on a bloqué sur les redefinition des fonction p_V, p_S...
*)


type var = A | B | C | D
type cons = O | I
type exp = V of var | C of cons
type axiom = S of ins * lis | E
and lis = Ax of axiom | E
and ins = Assign of var * exp | While of exp * ins | If of exp * ins * ins | E
