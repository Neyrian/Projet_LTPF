(* 
a:=1;
b:=1;
c:=1;
w(a){
 i(c){
  c:=0;
  a:=b
 }{
  b:=0;
  c:=a
 }
}

à l'aide d'une grammaire (définissant le langage while):

V pour variable1
C pour constante
E pour expression
I pour instruction

S pour axiome (tradition dans les grammaires)
L pour liste d'instructions

  S ::= IL | ε
  L ::= ;S | ε
  I ::= V:=E | i.E{S}{S} | w.E{S} | ε


*)

type mode = Nodebug | Debug

exception EchecParsing

let list_of_string s =
  let rec boucle s i n =
    if i = n then [] else s.[i] :: boucle s (i+1) n
  in boucle s 0 (String.length s)




type var = A | B | C | D
type cons = O | I
type exp = V of var | C of cons | N
type ins = Seq of ins * ins | Assign of var * exp | While of exp * ins | If of exp * ins * ins | Skip


type 't lazylist = unit -> 't contentsil
and 't contentsil = Nil | Cons of 't * 't lazylist;;

type ('r,'t) ranalist = 't lazylist -> 'r * 't lazylist

type ('r,'t) st = 't lazylist -> 'r

type 't analist = 't lazylist -> 't lazylist

let lazylist_of_string s =
  let rec boucle s i n =
    if i = n then fun () -> Nil else fun () ->  Cons(s.[i], (boucle s (i+1) n))
  in boucle s 0 (String.length s)


(* a suivi de b, ce dernier pouvant rendre un résultat *)
let (+>) (a : 'r analist) b =
  fun l -> let l = a l in b l

(* a rendant un résultat suivi de b, ce dernier pouvant rendre un résultat *)
let (++>) (a : ('r, 't) ranalist) b =
  fun l -> let (x, l) = a l in b x l

(* Choix entre a ou b *)
let (+|) (a : ('r, 't) st) (b : ('r, 't) st) =
  fun l -> try a l with EchecParsing -> b l

(* *)
let return : 'r -> ('r, 't) ranalist =
  fun x l -> (x, l)


let terminal c : 't analist = fun l -> match l () with
                                       | Cons(x, l) when x = c ->  l
                                       | _ -> raise EchecParsing

let assoc_var c: var = match c with
  | 'a' -> A
  | 'b' -> B
  | 'c' -> C
  | 'd' -> D
  | _ -> raise EchecParsing;;

let terminal_var c : ('r, 't) ranalist = fun l -> match l () with
  | Cons(x, l) -> ((assoc_var x), l)
  | _ -> raise EchecParsing


let p_V : (var, char) ranalist =
  fun l -> (terminal_var 'a' +| terminal_var 'b' +| terminal_var 'c' +| terminal_var 'd') l



let assoc_cons c: cons = match c with
  | '0' -> O
  | '1' -> I
  | _ -> raise EchecParsing;;

let terminal_cons c : ('r, 't) ranalist = fun l -> match l () with
  |Cons(x, l) -> ((assoc_cons x), l)
  | _ -> raise EchecParsing


let p_C : (cons, char) ranalist =
  fun l -> (terminal_cons '0' +| terminal_cons '1') l


let terminal_neg c : ('r, 't) ranalist = fun l -> match l () with
  | Cons(x, l) when x='#'-> (N, l)
  | _ -> raise EchecParsing

let p_N : (exp, char) ranalist =
  fun l -> terminal_neg '#' l

let p_E : (exp, char) ranalist =
  fun l -> ((p_V ++> fun v -> return (V(v)))
            +| (p_C ++> fun c -> return (C(c)))
           +|  (p_N ++> fun n -> return n)) l

let p_P : char analist =
  fun l -> terminal ';' l

let rec p_S : ('r, 't) ranalist =
  fun l -> (p_I ++> fun i -> (p_L ++> fun s -> return (Seq(i,s)))) l
and p_L : ('r, 't) ranalist =
  fun l ->  ((p_P +> p_S) +| (return Skip)) l

and p_I : ('r, 't) ranalist =
  fun l -> ((p_V ++> (fun v -> (terminal ':' +> (terminal '=' +> p_E)) ++> fun e -> return (Assign(v,e)) ))

            +| ((terminal 'i' +> (terminal '.' +> p_E)) ++>
                                   (fun e -> ((terminal '{' +> p_S) ++>
                                     (fun seq1 -> (terminal '}' +> (terminal '{' +> p_S) ++>
                                                     (fun seq2 -> (terminal '}' +> return (If(e, seq1, seq2)))))))))
            +| ((terminal 'w' +> (terminal '.' +> p_E) ++>
                                                                                                                                                                             (fun w -> (terminal '{' +> p_S ++>
                                                                                                                                                                                          (fun seq -> (terminal '}' +> return (While(w, seq))))))))) l
        



type state = E of assoc * state | Eps
and assoc = A of (var * cons);;

type config = CC of state * ins | CS of state;;


exception UnknownVal
exception NonSetVarNegation

let neg: cons -> cons =
  fun c -> if (c = O) then I else O

let rec update_aux: state -> var -> cons -> state =
  fun s v c_new ->
   match s with
   | E(A(v_act,c_act),s_suiv) -> if (v_act = v)
                                then E(A(v_act,c_new),s_suiv)
                                else E(A(v_act,c_act), (update_aux s_suiv v c_new))
   | Eps -> E(A(v,c_new), Eps);;

let rec get: state -> var -> cons =
  fun s v ->
  match s with
  | E(A(v_act,c_act),s_suiv) -> if (v_act = v)
                                then c_act
                                else get s_suiv v
  | Eps -> raise UnknownVal;;

let rec update: state -> var -> exp -> state =
  fun s v exp_new ->
  match exp_new with
  | V(v_exp) -> let c_new = get s v_exp in update_aux s v c_new
  | C(c) -> update_aux s v c
  | N -> let c_new = get s v in update_aux s v (neg c_new)
              



let eval_Expr: exp -> state -> bool =
  fun e s -> match e with
             | V(v) -> let r = get s v in if (r = I) then true else false
             | C(c) -> if (c = I) then true else false
             | N -> raise NonSetVarNegation


let rec faire_un_pas: ins -> state -> config =
  fun p s ->  match p with
                | Skip -> CS(s)
                | Assign(variable, affect) -> CS (update s variable affect)
                | Seq(seq1,seq2) -> (let resSeq1 = faire_un_pas seq1 s in
                                match resSeq1 with
                                | CS(sSeq1) -> CC(sSeq1, seq2)
                                | CC(sSeq1, pSeq1) -> CC(sSeq1, Seq(pSeq1, seq2)))
                | While(expr, inst) -> CC(s, (If(expr, Seq(inst, While(expr, inst)), Skip)))
                | If(expr, ins_true, ins_false) -> if (eval_Expr expr s) then CC(s, ins_true) else  CC(s, ins_false);;

                                
    
let setState: state -> state =
  fun s -> let sa = update s A (C(O)) in
           let sb = update sa B (C(O)) in
           let sc = update sb C (C(O)) in
           let sd = update sc D (C(O)) in sd;;

let reverse_cons :cons -> int =
  fun c ->
  match c with
  | O -> 0
  | I -> 1

let printStat: state -> unit =
  fun s -> Printf.printf "Var a = %u ;; Var b = %u ;; Var c = %u ;; Var d = %u\n"
             (reverse_cons (get s A)) (reverse_cons (get s B)) (reverse_cons (get s C)) (reverse_cons (get s D))
  
let rec executer_no_debug:  ins -> state -> state =
  fun p s -> let step = faire_un_pas p s in
             match step with
             | CS(s_final) -> s_final
             | CC(s_inter, p_suivant) -> executer_no_debug p_suivant s_inter



let scan_int () = Scanf.scanf " %d" (fun x -> x)
let scan_float () = Scanf.scanf " %f" (fun x -> x)
let scan_string () = Scanf.scanf " %s" (fun x -> x)
let scan_char () = Scanf.scanf "%c" (fun x -> x)
let waituser () = Scanf.scanf " %s" (ignore)

let rec executer_debug: int -> int list -> ins -> state -> state =
  fun n break_list p s ->
  flush_all ();
  if List.mem n break_list  then
    (Printf.printf "Break on : %u\n"n;
     printStat s;
     Printf.printf "Enter to continue...";
     waituser ();
     let step = faire_un_pas p s in
     match step with
     | CS(s_final) -> s_final
     | CC(s_inter, p_suivant) ->  executer_debug (n + 1) break_list p_suivant s_inter)
  else
    (Printf.printf "Step : %u\n" n;
    printStat s;
    let step = faire_un_pas p s in
      match step with
       | CS(s_final) -> s_final
       | CC(s_inter, p_suivant) -> executer_debug (n + 1) break_list p_suivant s_inter)




let rec getBreaks : int list -> int list =
  fun l ->  flush_all (); let cmd = list_of_string (scan_string ()) in
               match cmd with
               | 'b'::' '::n::[] -> flush_all ();  getBreaks ((int_of_char n)::l)
               | 'r'::[] -> flush_all (); l
               | _ -> flush_all (); print_string "Unvalid command\n";  getBreaks l
  
let rec executer : mode -> ins -> state -> state =
  fun mode p s ->
  match mode with
  | Nodebug -> print_string "No Debug mode\n";
               executer_no_debug p s
  | Debug -> print_string "Debug Mode\nOptions : \nb n =  breaks step n\nr = to run the prog\n";
             let b:int list = getBreaks [] in
             executer_debug 0 b p s
