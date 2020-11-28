#use "projet.ml";;


let exec : 'a -> state =
  fun st ->
  let prog = lazylist_of_string st in let s : state = setState Eps in
                                      let myprog_pars = p_S prog in
                                      match myprog_pars with (i, res) -> if res () = Nil then executer i s else raise EchecParsing;;

print_string "A chaque test, l'environnement est remis a zeros";;
print_string "Test Assign";;

exec "a:=1";;
exec "a:=#";;
exec "a=1";;
exec "z:=1";;
exec "a:=";;

print_string "Test Seq";;
exec "a:=1;b:=1";;
exec "a:=1;b:=1;b:=0";;
exec "a:=1/b:=1";;

print_string "Test_If";;
exec "a:=1;i.a{b:=1}{c:=1}";;
exec "i.a{b:=1}{c:=1}";;
exec "a:=1;i.a{b:=1}{}";;
exec "ia{b:=1}{c:=1}";;
exec "i.a{c:=1}";;
exec "a:=1;i.a{b:=1{c:=1}";;
exec "i.a{b:=1{c:=1}";;

print_string "Test_While";;
exec "a:=1;w.a{b:=1;a:=0}";;
exec "w.a{b:=1;a:=0}";;
exec "w.a{b:=1;a:=0";;
exec "a:=1;wa{b:=1;a:=0}";;


print_string "Test on complex prog";;
exec "a:=1;b:=1;c:=1;w.a{i.c{c:=0;a:=b}{b:=0;c:=a;d:=1}}";;

