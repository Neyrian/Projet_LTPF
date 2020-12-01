#load "src/grammar.cmo";;
#load "src/parser.cmo";;
#load "src/SOS.cmo";;

let setState: state -> state =
  fun s -> let sa = update s A (C(O)) in
           let sb = update sa B (C(O)) in
           let sc = update sb C (C(O)) in
           let sd = update sc D (C(O)) in sd;;

let rec executer : ins -> state -> state =
  fun p s -> let step = faire_un_pas p s in
             match step with
             | CS(s_final) -> s_final
             | CC(s_inter, p_suivant) -> executer p_suivant s_inter



