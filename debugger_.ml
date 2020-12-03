(*#load "parser_.cmo";;
#load "SOS_.cmo";;
#load "main_.cmo";;*)

let prog = "a:=1;b:=1;c:=1;w.a{i.c{c:=0;a:=b}{b:=0;c:=a;d:=1}}";;

let header () = print_string "================ DEBUGGER ================\nProgram :\n\t"; print_string prog; print_string "\nOptions : \n\tb n\tbreak on step n\n\tr\tto run the prog\n==========================================\n";;

let tester : 'a -> unit =
  fun st -> 
  let prog = Parser_.lazylist_of_string st in
  let s : SOS_.state = Main_.setState Eps in
  try
    let myprog_pars = Parser_.p_S prog in
    match myprog_pars with (i, res) ->
      if res () = Nil
      then let r = header () in ignore r; let r = Main_.executer Main_.Debug i s in ignore r;  print_newline ()
      else print_string (String.concat "" ["FAILED PARSING for : "; st; "\n"])
  with Parser_.EchecParsing -> print_string (String.concat "" ["FAILED PARSING for : "; st; "\n"]);;

tester prog;;
