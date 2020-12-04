(*#load "grammar.cmo";;*)

(*We couldn't parse the thing we're reading*)
exception EchecParsing;;

(*=== Used for data manipulations ===*)

(*Lazylist, used to hold the content of the program, char by char*)
type 't lazylist = unit -> 't contentsil
and 't contentsil = Nil | Cons of 't * 't lazylist;;

(*Converts a String to a lazylist*)
let lazylist_of_string s =
  let rec boucle s i n =
    if i = n then fun () -> Nil else fun () ->  Cons(s.[i], (boucle s (i+1) n))
  in boucle s 0 (String.length s)

(*Used for decreasing the lazylist while making the AST*)
type ('r,'t) ranalist = 't lazylist -> 'r * 't lazylist

(*returns the Node associate to the Char*)
type ('r,'t) st = 't lazylist -> 'r

(*Used when we read one char, returns the list without this one.*)
type 't analist = 't lazylist -> 't lazylist

(* a suivi de b, ce dernier pouvant rendre un résultat *)
let (+>) (a : 'r analist) b =
  fun l -> let l = a l in b l

(* a rendant un résultat suivi de b, ce dernier pouvant rendre un résultat *)
let (++>) (a : ('r, 't) ranalist) b =
  fun l -> let (x, l) = a l in b x l

(* Choix entre a ou b *)
let (+|) (a : ('r, 't) st) (b : ('r, 't) st) =
  fun l -> try a l with EchecParsing -> b l

let return : 'r -> ('r, 't) ranalist =
  fun x l -> (x, l)

(*=== Terminal functions used by the parser ===*)

let rec terminal c : 't analist = fun l -> match l () with
                                           | Cons('\t', l) -> (terminal c) l
                                           | Cons('\n', l) -> (terminal c) l
                                           | Cons(' ', l) -> (terminal c) l
                                           | Cons(x, l) when x = c -> l
                                           | _ -> raise EchecParsing

let assoc_var c: Grammar_.var = match c with
  | 'a' -> Grammar_.A
  | 'b' -> Grammar_.B
  | 'c' -> Grammar_.C
  | 'd' -> Grammar_.D
  | _ -> raise EchecParsing;;

let rec terminal_var c : ('r, 't) ranalist = fun l -> match l () with
                                                      | Cons('\t', l) -> (terminal_var c) l
                                                      | Cons('\n', l) -> (terminal_var c) l
                                                      | Cons(' ', l) -> (terminal_var c) l
                                                      | Cons(x, l) -> ((assoc_var x), l)
                                                      | _ -> raise EchecParsing

let assoc_cons c: Grammar_.cons = match c with
  | '0' -> Grammar_.O
  | '1' -> Grammar_.I
  | _ -> raise EchecParsing;;

let rec terminal_cons c : ('r, 't) ranalist = fun l -> match l () with
                                                       | Cons('\t', l) -> (terminal_cons c) l
                                                       | Cons('\n', l) -> (terminal_cons c) l
                                                       | Cons(' ', l) -> (terminal_cons c) l
                                                       | Cons(x, l) -> ((assoc_cons x), l)
                                                       | _ -> raise EchecParsing

let rec terminal_neg c : ('r, 't) ranalist = fun l -> match l () with
                                                      | Cons('\t', l) -> (terminal_neg c) l
                                                      | Cons('\n', l) -> (terminal_neg c) l
                                                      | Cons(' ', l) -> (terminal_neg c) l
                                                      | Cons(x, l) when x='#'-> (Grammar_.N, l)
                                                      | _ -> raise EchecParsing

(*=== The PARSER for the GRAMMAR that will build the correct AST ===*)

let p_V : (Grammar_.var, char) ranalist =
  fun l -> (terminal_var 'a' +| terminal_var 'b' +| terminal_var 'c' +| terminal_var 'd') l

let p_C : (Grammar_.cons, char) ranalist =
  fun l -> (terminal_cons '0' +| terminal_cons '1') l

let p_N : (Grammar_.exp, char) ranalist =
  fun l -> terminal_neg '#' l

let p_E : (Grammar_.exp, char) ranalist =
  fun l -> ((p_V ++> fun v -> return (Grammar_.V(v)))
            +| (p_C ++> fun c -> return (Grammar_.C(c)))
            +|  (p_N ++> fun n -> return n)) l

let p_P : char analist =
  fun l -> terminal ';' l

let rec p_S : ('r, 't) ranalist =
  fun l -> (p_I ++> fun i -> (p_L ++> fun s -> return (Grammar_.Seq(i,s)))) l
and p_L : ('r, 't) ranalist =
  fun l ->  ((p_P +> p_S) +| (return Grammar_.Skip)) l

and p_I : ('r, 't) ranalist =
  fun l -> ((p_V ++> (fun v -> (terminal ':' +> (terminal '=' +> p_E)) ++> fun e -> return (Grammar_.Assign(v,e)) ))
            +| ((terminal 'i' +> (terminal '.' +> p_E)) ++>
                  (fun e -> ((terminal '{' +> p_S) ++>
                               (fun seq1 -> (terminal '}' +> (terminal '{' +> p_S) ++>
                                               (fun seq2 -> (terminal '}' +> return (Grammar_.If(e, seq1, seq2)))))))))
            +| ((terminal 'w' +> (terminal '.' +> p_E) ++>
                   (fun w -> (terminal '{' +> p_S ++>
                                (fun seq -> (terminal '}' +> return (Grammar_.While(w, seq))))))))) l;;
