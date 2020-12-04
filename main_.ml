(*#load "grammar_.cmo";;
#load "SOS_.cmo";;*)

(*Will define the exeution mode*)
type mode = Nodebug | Debug

(*init all variables in *)
let set_state: SOS_.state -> SOS_.state =
  fun s -> let st = SOS_.update s Grammar_.A (Grammar_.C(O)) in
           let st = SOS_.update st Grammar_.B (Grammar_.C(O)) in
           let st = SOS_.update st Grammar_.C (Grammar_.C(O)) in
           SOS_.update st Grammar_.D (Grammar_.C(O));;

(*print all variable values in the given state*)
let print_state: SOS_.state -> unit =
  fun s -> Printf.printf "A = \027[1m%u\027[0m / B = \027[1m%u\027[0m / C = \027[1m%u\027[0m / D = \027[1m%u\027[0m\n"
           (SOS_.reverse_cons (SOS_.get s Grammar_.A)) 
           (SOS_.reverse_cons (SOS_.get s Grammar_.B)) 
           (SOS_.reverse_cons (SOS_.get s Grammar_.C)) 
           (SOS_.reverse_cons (SOS_.get s Grammar_.D))
  
(* return true if the user wants to continue, false if wants to go to next step*)
let rec wait_user_input () = flush_all (); let cmd = Utils_.list_of_string (read_line ()) in 
               match cmd with
               | 'n'::_ -> false
               | 'c'::_ -> true
               | _ -> print_string "Unvalid command\n";
                      wait_user_input ()

(*function that will parse the user input to setup the different breakpoints*)
let rec get_breaks : int list -> int list =
  fun l -> flush_all (); let cmd = Utils_.list_of_string (read_line ()) in 
               match cmd with
               | 'b'::' '::n -> let x = Utils_.list_char_to_int n 0 in
                        print_string "Break on line : ";
                        print_int x;
                        print_newline ();
                        get_breaks (x::l)
               | 'r'::_ -> l
               | 'n'::_ -> print_string "Error: program is not running...\n";
                           get_breaks l
               | 'c'::_ -> print_string "Error: program is not running...\n";
                           get_breaks l
               | _ -> print_string "Unvalid command\n";
                      get_breaks l

(*run according to the current step number and the int list of beakpoints*)
let rec executer_debug: int -> int list -> Grammar_.ins -> SOS_.state -> SOS_.state =
  fun n break_list p s ->
  if List.mem n break_list then (*there is a breakpoint now*)
    (Printf.printf "Break on step#%u\t " n;
     print_state s;
     let step = SOS_.faire_un_pas p s in
     match step with
     | SOS_.CS(s_final) -> s_final
     | SOS_.CC(s_inter, p_suiv) -> (if (wait_user_input ()) 
                                   then executer_debug (n + 1) break_list p_suiv s_inter
     															 else executer_debug (n + 1) ((n+1)::break_list) p_suiv s_inter))
  else (*run until next breakpoint*)
    (Printf.printf "Step#%u\t " n;
    print_state s;
    let step = SOS_.faire_un_pas p s in
      match step with
       | SOS_.CS(s_final) -> s_final
       | SOS_.CC(s_inter, p_suiv) -> executer_debug (n + 1) break_list p_suiv s_inter)

(*the basic runner to consume the differents steps*)
let rec executer_no_debug: Grammar_.ins -> SOS_.state -> SOS_.state =
  fun p s -> let step = SOS_.faire_un_pas p s in
             match step with
             | SOS_.CS(s_final) -> s_final
             | SOS_.CC(s_inter, p_suiv) -> executer_no_debug p_suiv s_inter

(*Regarding the mode, we run the approriate runner.*)
let rec executer : mode -> Grammar_.ins -> SOS_.state -> SOS_.state =
  fun mode p s ->
  match mode with
  | Nodebug -> executer_no_debug p s
  | Debug -> let b:int list = get_breaks [] in
             executer_debug 0 b p s


