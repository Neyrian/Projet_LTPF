(*#load "grammar.cmo";;*)

(*Describe the current program state*)
type state = E of assoc * state | Eps
and assoc = A of (Grammar_.var * Grammar_.cons);;

(*Describe the current program state with the actual 
values of variables in the grammar at this state*)
type config = CC of state * Grammar_.ins | CS of state;;

(*We can't this variable or the expression is unclear*)
exception UnknownVal;;

(*Negates the associate variable*)
let neg: Grammar_.cons -> Grammar_.cons =
  fun c -> if (c = Grammar_.O) then Grammar_.I else Grammar_.O

(*change the value of var v by cons c_new in the current state*)
let rec update_aux: state -> Grammar_.var -> Grammar_.cons -> state =
  fun s v c_new ->
  match s with
  | E(A(v_act,c_act),s_suiv) -> if (v_act = v)
                                then E(A(v_act,c_new),s_suiv)
                                else E(A(v_act,c_act), (update_aux s_suiv v c_new))
  | Eps -> E(A(v,c_new), Eps);;

(*get the value of the var v in state s*)
let rec get: state -> Grammar_.var -> Grammar_.cons =
  fun s v ->
  match s with
  | E(A(v_act,c_act),s_suiv) -> if (v_act = v)
                                then c_act
                                else get s_suiv v
  | Eps -> raise UnknownVal;;

(*will call update_aux to update the approriate variable 
with the new value in the current state s*)
let rec update: state -> Grammar_.var -> Grammar_.exp -> state =
  fun s v exp_new ->
  match exp_new with
  | V(v_exp) -> let c_new = get s v_exp in update_aux s v c_new
  | C(c) -> update_aux s v c
  | N -> let c_new = get s v in update_aux s v (neg c_new)

(*Used to tell if a IF statement should be in the 
"then" section or "else" section. Bassically it 
converts I to true and O to false*)
let eval_Expr: Grammar_.exp -> state -> bool =
  fun e s -> match e with
             | V(v) -> let r = get s v in if (r = Grammar_.I) then true else false
             | C(c) -> if (c = Grammar_.I) then true else false
             | N -> raise UnknownVal

(*make a step in the AST desribe by ins*)
let rec faire_un_pas: Grammar_.ins -> state -> config =
  fun p s ->  match p with
              | Skip -> CS(s)
              | Assign(variable, affect) -> CS (update s variable affect)
              | Seq(seq1,seq2) -> (let resSeq1 = faire_un_pas seq1 s in
                                   match resSeq1 with
                                   | CS(sSeq1) -> CC(sSeq1, seq2)
                                   | CC(sSeq1, pSeq1) -> CC(sSeq1, Seq(pSeq1, seq2)))
              | While(expr, inst) -> CC(s, (If(expr, Seq(inst, While(expr, inst)), Skip)))
              | If(expr, ins_true, ins_false) -> if (eval_Expr expr s) then CC(s, ins_true) else  CC(s, ins_false);;

