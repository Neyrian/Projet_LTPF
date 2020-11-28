exception Echec
type analist = char list -> char list

(* Généralisation *)
let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

let p_variable : analist = fun l ->
  match l with
  | 'a' :: l -> l
  | 'b' :: l -> l
  | 'c' :: l -> l
  | 'd' :: l -> l
  | _ -> raise Echec

let p_constante : analist = fun l ->
  match l with
  | '0' :: l -> l
  | '1' :: l -> l
  | _ -> raise Echec

let p_expression : analist = fun l ->
  try p_variable l with Echec -> p_constante l

let p_affectation : analist = fun l ->
  let l1 = p_variable l in
  let l2 = terminal ':' l1 in
  let l3 = terminal '=' l2 in
  p_expression l3


let rec p_axiome : analist = fun l ->
  try p_instruclist l with Echec -> p_epsilon l

and p_epsilon : analist = fun l -> l

and p_instruclist : analist = fun l ->
  let l1 = p_instruction l in
  p_liste l1

and p_liste : analist = fun l ->
  match l with
    | ';'::l -> p_axiome l
    | _ -> p_epsilon l

and p_if : analist = fun l ->
  let l1 = terminal 'i' l in
  let l2 = terminal '.' l1 in
  let l3 = p_expression l2 in
  let l4 = terminal '{' l3 in
  let l5 = p_axiome l4 in
  let l6 = terminal '}' l5 in
  let l7 = terminal '{' l6 in
  let l8 = p_axiome l7 in
  terminal '}' l8

and p_while : analist = fun l ->
  let l1 = terminal 'w' l in
  let l2 = terminal '.' l1 in
  let l3 = p_expression l2 in
  let l4 = terminal '{' l3 in
  let l5 = p_axiome l4 in
  terminal '}' l5

and p_instruction : analist = fun l ->
  try p_affectation l with Echec -> (try p_if l with Echec -> (try p_while l with Echec -> p_epsilon l))

(* Grammaire récursive
    S1 ::= '(' S ')'
    S2 ::= 'x'
    S  ::= S1 | S2

    V ::= a | b | c | d
    C ::= 0 | 1
    E ::= V | C

  S ::= IL | ε
  L ::= ;S | ε
  I ::= V:=E | i.E{S}{S} | w.E{S} | ε
*)

(* let rec p_S : analist =
  let p_S1 : analist = fun l ->
    let l = terminal '(' l in
    let l = p_S l in
    let l = terminal ')' l in
    l
  and p_S2 : analist = fun l ->
    let l = terminal 'x' l in
    l in
  fun l ->
  try p_S1 l with Echec -> p_S2 l *)

let list_of_string s =
  let rec boucle s i n =
    if i = n then [] else s.[i] :: boucle s (i+1) n
  in boucle s 0 (String.length s)

let isValid = fun s -> match p_axiome (list_of_string s) with
                              | [] -> true
                              |  _ -> false
;;
