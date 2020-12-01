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
      then let r = Main_.executer i s in match r with _ -> print_string "PASSED\n"
      else print_string (String.concat "" ["FAILED with : "; st; "\n"])
  with Parser_.EchecParsing -> print_string (String.concat "" ["FAILED with : "; st; "\n"]);;

print_string "A chaque test, l'environnement est remis a zeros\n";;
print_string "\nTest_Assign\n";;
tester "a:=1";;
tester "a:=#";;
tester "a=1";;
tester "z:=1";;
tester "a:=";;

print_string "\nTest_Seq\n";;
tester "a:=1;b:=1";;
tester "a:=1;b:=1;b:=0";;
tester "a:=1/b:=1";;

print_string "\nTest_If\n";;
tester "a:=1;i.a{b:=1}{c:=1}";;
tester "i.a{b:=1}{c:=1}";;
tester "a:=1;i.a{b:=1}{}";;
tester "ia{b:=1}{c:=1}";;
tester "i.a{c:=1}";;
tester "a:=1;i.a{b:=1{c:=1}";;
tester "i.a{b:=1{c:=1}";;

print_string "\nTest_While\n";;
tester "a:=1;w.a{b:=1;a:=0}";;
tester "w.a{b:=1;a:=0}";;
tester "w.a{b:=1;a:=0";;
tester "a:=1;wa{b:=1;a:=0}";;

print_string "\nTest on complex prog\n";;
tester "a:=1;b:=1;c:=1;w.a{i.c{c:=0;a:=b}{b:=0;c:=a;d:=1}}";;
