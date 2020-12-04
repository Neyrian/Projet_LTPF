(* 
Grammaire :

V pour variable1
C pour constante
E pour expression
I pour instruction

S pour axiome (tradition dans les grammaires)
L pour liste d'instructions

 *S ::= IL | ε
  L ::= ;S | ε
  I ::= V:=E | i.E{S}{S} | w.E{S} | ε

*)

(*Déclaration des types utilisés pour la grammaire ci-dessus*)
type var = A | B | C | D
type cons = O | I 
type exp = V of var | C of cons | N
type ins = Seq of ins * ins | Assign of var * exp | While of exp * ins | If of exp * ins * ins | Skip
