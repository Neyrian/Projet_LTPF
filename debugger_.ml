(*#load "parser_.cmo";;
#load "SOS_.cmo";;
#load "main_.cmo";;*)

(*Programme debuggé, peut être modifié !*)
let prog = "a := 1;
b := 1;
c:=1;
w.a {
	i.c {
		c :=0;
		a :=b 
	}
	{
		b := 0;
		c := a;
		d := 1
	}
}";;

(*Header du debugger.*)
let header () = print_string "\027[01m================ \027[05mDEBUGGER\027[0;1m ================
\027[0;4mProgram :\027[0;36m

"; print_string prog; print_string "

\027[0;4mOptions :\027[0m 
 - \027[4mbefore running :\027[0m 
\t\027[01mb \027[93mn\027[0m\tbreak on step \027[93mn
\t\027[0;1mr\027[0m\tto run the prog
 - \027[4mduring the run :\027[0m 
\t\027[1mc\027[0m\tto continue
\t\027[1mn\027[0m\tto step forward
\027[01m==========================================\027[0m\n";;

(*function that will create the initial state and call the runner in debug mode*)
let tester : 'a -> unit =
  fun st -> 
  let prog = Parser_.lazylist_of_string st in
  let s : SOS_.state = Main_.set_state Eps in
  try
    let myprog_pars = Parser_.p_S prog in
    match myprog_pars with (i, res) ->
      if res () = Nil
      then let r = header () in ignore r; let r = Main_.executer Main_.Debug i s in ignore r;  print_newline ()
      else print_string (String.concat "" ["\027[31mFAILED PARSING\027[0m for : \n"; st; "\n"])
  with Parser_.EchecParsing -> print_string (String.concat "" ["\027[31mFAILED PARSING\027[0m for : \n"; st; "\n"]);;

tester prog;;
