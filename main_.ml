(*#load "grammar_.cmo";;
#load "SOS_.cmo";;*)

type mode = Nodebug | Debug

let setState: SOS_.state -> SOS_.state =
  fun s -> let sa = SOS_.update s Grammar_.A (Grammar_.C(O)) in
           let sb = SOS_.update sa Grammar_.B (Grammar_.C(O)) in
           let sc = SOS_.update sb Grammar_.C (Grammar_.C(O)) in
           let sd = SOS_.update sc Grammar_.D (Grammar_.C(O)) in sd;;

let reverse_cons : Grammar_.cons -> int =
  fun c ->
  match c with
  | Grammar_.O -> 0
  | Grammar_.I -> 1
  
let print_state: SOS_.state -> unit =
  fun s -> Printf.printf "Var a = %u ;; Var b = %u ;; Var c = %u ;; Var d = %u\n"
             (reverse_cons (SOS_.get s Grammar_.A)) (reverse_cons (SOS_.get s Grammar_.B)) (reverse_cons (SOS_.get s Grammar_.C)) (reverse_cons (SOS_.get s Grammar_.D))
  
let rec executer_no_debug: Grammar_.ins -> SOS_.state -> SOS_.state =
  fun p s -> let step = SOS_.faire_un_pas p s in
             match step with
             | SOS_.CS(s_final) -> s_final
             | SOS_.CC(s_inter, p_suivant) -> executer_no_debug p_suivant s_inter

(* return true if continue, else false*)
let rec waituser () = flush_all (); let cmd = Parser_.list_of_string (read_line ()) in 
               match cmd with
               | 'n'::_ -> false
               | 'c'::_ -> true
               | _ -> print_string "Unvalid command\n";
                      waituser ()

let rec executer_debug: int -> int list -> Grammar_.ins -> SOS_.state -> SOS_.state =
  fun n break_list p s ->
  if List.mem n break_list  then
    (Printf.printf "Break on : %u\n"n;
     print_state s;
     (if waituser ()
      then (*continue*)
          let step = SOS_.faire_un_pas p s in
          match step with
          | SOS_.CS(s_final) -> s_final
          | SOS_.CC(s_inter, p_suivant) ->  executer_debug (n + 1) break_list p_suivant s_inter
     else (*next step*)
        let step = SOS_.faire_un_pas p s in
          match step with
          | SOS_.CS(s_final) -> s_final
          | SOS_.CC(s_inter, p_suivant) ->  executer_debug (n + 1) ((n+1)::break_list) p_suivant s_inter)
    )
  else
    (Printf.printf "Step : %u\n" n;
    print_state s;
    let step = SOS_.faire_un_pas p s in
      match step with
       | SOS_.CS(s_final) -> s_final
       | SOS_.CC(s_inter, p_suivant) -> executer_debug (n + 1) break_list p_suivant s_inter)

let convert_char_int: char -> int =
  fun c -> (int_of_char c) - 48


let rec list_char_to_int: char list -> int -> int=
  fun l x ->
  match l with
  | y::l -> list_char_to_int l (x * 10 + (convert_char_int y))
  | [] -> x

let rec getBreaks : int list -> int list =
  fun l -> flush_all (); let cmd = Parser_.list_of_string (read_line ()) in 
               match cmd with
               | 'b'::' '::n -> let x = list_char_to_int n 0 in
                        print_string "Break on line : ";
                        print_int x;
                        print_newline ();
                        getBreaks (x::l)
               | 'r'::_ -> l
               | 'n'::_ -> print_string "Error: program is not running...\n";
                           getBreaks l
               | 'c'::_ -> print_string "Error: program is not running...\n";
                           getBreaks l
               | _ -> print_string "Unvalid command\n";
                      getBreaks l

let rec executer : mode -> Grammar_.ins -> SOS_.state -> SOS_.state =
  fun mode p s ->
  match mode with
  | Nodebug -> executer_no_debug p s
  | Debug -> let b:int list = getBreaks [] in
             executer_debug 0 b p s
             
             
             

