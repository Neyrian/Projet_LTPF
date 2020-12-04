(*#load "parser_.cmo";;
#load "SOS_.cmo";;
#load "main_.cmo";;*)

let tester : 'a -> unit =
  fun st -> 
  let prog = Parser_.lazylist_of_string st in
  let s : SOS_.state = Main_.setState Eps in
  try
    let myprog_pars = Parser_.p_S prog in
    match myprog_pars with (i, res) ->
      if res () = Nil
      then let r = Main_.executer Main_.Nodebug i s in print_string (String.concat "" ["PASSED with : "; st; "\n"]); Main_.print_state r; print_newline ();
      else print_string (String.concat "" ["FAILED PARSING (end of program not recognized) for : "; st; "\n"])
  with Parser_.EchecParsing -> print_string (String.concat "" ["FAILED PARSING for : "; st; "\n"]);;

print_string "A chaque test, l'environnement est remis à zéro\n";;
print_string "\n\n\t== Test_Assign ==\n\n";;
tester "a:=1";;
tester "a := 1";;
tester "	a := 1";;
tester "a:=#";;
tester "a=1";;
tester "z:=1";;
tester "a:=";;

print_string "\n\n\t== Test_Seq ==\n\n";;
tester "a:=1;b:=1";;
tester "\n\ta := 1;\n\tb := 1";;
tester "a:=1;b:=1;b:=0";;
tester "a:=1/b:=1";;

print_string "\n\n\t== Test_If ==\n\n";;
tester "\na:=1;\ni.a{\n\tb:=1\n}{\n\tc:=1\n}";;
tester "i.a{b:=1}{c:=1}";;
tester "a:=1;i.a{b:=1}{}";;
tester "ia{b:=1}{c:=1}";;
tester "i.a{c:=1}";;
tester "a:=1;i.a{b:=1{c:=1}";;
tester "i.a{b:=1{c:=1}";;

print_string "\n\n\t== Test_While ==\n\n";;
tester "a:=1;w.a{b:=1;a:=0}";;
tester "w.a{b:=1;a:=0}";;
tester "w.a{b:=1;a:=0";;
tester "a:=1;wa{b:=1;a:=0}";;

print_string "\n\n\t== Test on complex prog ==\n\n";;
tester "a:=1;b:=1;c:=1;w.a{i.c{c:=0;a:=b}{b:=0;c:=a;d:=1}}";;
