(*#load "grammar_.cmo";;
#load "SOS_.cmo";;*)

let setState: SOS_.state -> SOS_.state =
  fun s -> let sa = SOS_.update s Grammar_.A (Grammar_.C(O)) in
           let sb = SOS_.update sa Grammar_.B (Grammar_.C(O)) in
           let sc = SOS_.update sb Grammar_.C (Grammar_.C(O)) in
           let sd = SOS_.update sc Grammar_.D (Grammar_.C(O)) in sd;;

let rec executer : Grammar_.ins -> SOS_.state -> SOS_.state =
  fun p s -> let step = SOS_.faire_un_pas p s in
             match step with
             | SOS_.CS(s_final) -> s_final
             | SOS_.CC(s_inter, p_suivant) -> executer p_suivant s_inter



