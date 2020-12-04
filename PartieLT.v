(* TD9 - Sémantique petit pas                *)
(* Structural Operational Semantics (SOS)    *)


(* On importe les bibliothèques de Coq utiles pour le TD   *)

Require Import Bool Arith List.
Import List.ListNotations.

(* ============================================================================= *)
(** * Préliminaires *)
(** ** Syntaxe des expressions arithétiques *)

Inductive Aexp :=
| Aco : nat -> Aexp (** constantes *)
| Ava : nat -> Aexp (** variables *)
| Apl : Aexp -> Aexp -> Aexp
| Amu : Aexp -> Aexp -> Aexp
| Amo : Aexp -> Aexp -> Aexp
.

(** ** Syntaxe des expressions booléennes *)

Inductive Bexp :=
| Btrue : Bexp
| Bfalse : Bexp
| Bnot : Bexp -> Bexp
| Band : Bexp -> Bexp -> Bexp
| Bor : Bexp -> Bexp -> Bexp
| Beq : Bexp -> Bexp -> Bexp    (* test égalité de Bexp *)
| Beqnat : Aexp -> Aexp -> Bexp (* test égalité de Aexp *)
.

(** ** Syntaxe du langage impératif WHILE *)

Inductive Winstr :=
| Skip   : Winstr
| Assign : nat -> Aexp -> Winstr
| Seq    : Winstr -> Winstr -> Winstr
| If     : Bexp -> Winstr -> Winstr -> Winstr
| While  : Bexp -> Winstr -> Winstr
.

(* -------------------------------------------------- *)
(** ** États *)

Definition state := list nat.


Fixpoint get (x:nat) (s:state) : nat :=
match x,s with
| 0   , v::_      => v
| S x1, _::l1 => get x1 l1
| _   , _         => 0
end.


Fixpoint update (s:state) (v:nat) (n:nat): state :=
match v,s with
| 0   , a :: l1 => n :: l1
| 0   , nil     => n :: nil
| S v1, a :: l1 => a :: (update l1 v1 n)
| S v1, nil     => 0 :: (update nil v1 n)
end.

(* ----------------------------------------------- *)
(** ** Sémantique fonctionnelle de Aexp et de Bexp *)

Fixpoint evalA (a: Aexp) (s: state) : nat :=
  match a with
  | Aco n => n
  | Ava x => get x s
  | Apl a1 a2 =>  evalA a1 s + evalA a2 s
  | Amu a1 a2 =>  evalA a1 s * evalA a2 s
  | Amo a1 a2 =>  evalA a1 s - evalA a2 s
  end.

Definition eqboolb b1 b2 : bool :=
  match b1, b2  with
  | true , true  => true
  | false, false => true
  | _    , _     => false
  end.

Fixpoint eqnatb n1 n2 : bool :=
  match n1, n2 with
  | O    , O     => true
  | S n1', S n2' => eqnatb n1' n2'
  | _    , _     => false
  end.

Fixpoint evalB (b : Bexp) (s : state) : bool :=
  match b with
  | Btrue => true
  | Bfalse => false
  | Bnot b => negb (evalB b s)
  | Band e1 e2 => (evalB e1 s) && (evalB e2 s)
  | Bor e1 e2 => (evalB e1 s) || (evalB e2 s)
  | Beq e1 e2 => eqboolb (evalB e1 s) (evalB e2 s)
  | Beqnat n1 n2 => eqnatb (evalA n1 s) (evalA n2 s)
  end.


(* ================================================================================ *)

(** * SOS (Sémantique opérationnelle à petits pas) du langage While *)

Inductive config :=
| Inter : Winstr -> state -> config
| Final : state -> config.

(* La relation pour un pas de SOS *)

Inductive SOS_1: Winstr -> state -> config -> Prop :=
| SOS_Skip     : forall s,
                 SOS_1 Skip s (Final s)

| SOS_Assign   : forall x a s,
                 SOS_1 (Assign x a) s (Final (update s x (evalA a s)))

| SOS_Seqf     : forall i1 i2 s s1,
                 SOS_1 i1 s (Final s1) ->
                 SOS_1 (Seq i1 i2) s (Inter i2 s1)
| SOS_Seqi     : forall i1 i1' i2 s s1,
                 SOS_1 i1 s (Inter i1' s1) ->
                 SOS_1 (Seq i1 i2) s (Inter (Seq i1' i2) s1)

| SOS_If_true  : forall b i1 i2 s,
                 evalB b s = true  ->
                 SOS_1 (If b i1 i2) s (Inter i1 s)
| SOS_If_false : forall b i1 i2 s,
                 evalB b s = false ->
                 SOS_1 (If b i1 i2) s (Inter i2 s)

| SOS_While    : forall b i s,
                 SOS_1 (While b i) s (Inter (If b (Seq i (While b i)) Skip) s)
.

(** Fermeture réflexive-transitive de SOS_1 *)
(** Cette sémantique donne toutes les configurations atteignables
    par un (AST de) programme en partant d'un état initial.
 *)

Inductive SOS : config -> config -> Prop :=
| SOS_stop  : forall c, SOS c c
| SOS_again : forall i1 s1 c2 c3,
              SOS_1 i1 s1 c2 -> SOS c2 c3 ->
              SOS (Inter i1 s1) c3.


(* ================================================================================ *)

Definition N0 := Aco 0.
Definition N1 := Aco 1.
Definition N2 := Aco 2.
Definition N3 := Aco 3.
Definition N4 := Aco 4.


(** * I *)

(** *** Calcul du carré avec des additions *)
(** On code dans While un programme Pcarre correspondant à
    while not (i=n) do {i:= 1+i; x:= y+x ; y:= 2+y} *)
Definition Il := 0.
Definition Ir := Ava Il.
Definition Xl := 1.
Definition Xr := Ava Xl.
Definition Yl := 2.
Definition Yr := Ava Yl.

Definition incrI := Assign Il (Apl N1 Ir).
Definition incrX := Assign Xl (Apl Yr Xr).
Definition incrY := Assign Yl (Apl N2 Yr).
Definition corps_carre := Seq incrI (Seq incrX incrY).
Definition Pcarre_2 := While (Bnot (Beqnat Ir (Aco 2))) corps_carre.
Definition Pcarre n := While (Bnot (Beqnat Ir (Aco n))) corps_carre.
(** Nouveau : on peut jouer avec des programmes qui bouclent *)
Definition Pcarre_inf := While Btrue corps_carre.


(* 12.a) Propriété de transitivité de SOS *)

Theorem SOS_trans : forall c1 c2 c3, SOS c1 c2 -> SOS c2 c3 -> SOS c1 c3.
Proof.
  intros.
  induction H as [ | ].
  - apply H0.
  - eapply SOS_again. apply H. apply IHSOS. apply H0.
Qed.

(* 12.b) La propriété SOS_seq  *)
(* L'énoncé peut être vu comme une implication (c'est en réalité une fonction qui prend en 
argument une configuration qui vérifie la propriété so) : Si on a besoin de n pas en partant de 
la configuration intermédiaire comportant l'instruction i1 et l'état s1 afin d'arriver à la 
configuration finale ayant l'état s2, cela signifie qu'on aura besoin de n pas en partant de
la configuration comportant l'instruction i1;i2 et l'état s1 afin d'arriver dans la configuration
intermédiare comportant l'instruction i2 et l'état s2. *) 
Fixpoint SOS_seq i1 i2 s1 s2 (so : SOS (Inter i1 s1) (Final s2)) :
  SOS (Inter (Seq i1 i2) s1) (Inter i2 s2).
Proof.
  intros.
  eapply SOS_again.
  - apply SOS_Seqf. 
Admitted.

(* 13.a) *)

Lemma SOS_Pcarre_2_1er_tour : SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  { cbv.  apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. apply SOS_Assign. }
  cbn.  apply SOS_stop.
Qed.

(* 13.b) L'énoncé signifie que lorsque qu'on exécute le programme Pcarre_inf en partant de *)
(*       l'état [i = 0 ; x = 0 ; y = 1], on arrive à une configuration intermédiaire où Pcarre_inf peut être exécuté *)
(*       en partant de l'état [i = 1 ; x = 1; y = 3] *)


Theorem SOS_Pcarre_inf_1er_tour : SOS (Inter Pcarre_inf [0;0;1]) (Inter Pcarre_inf [1; 1; 3]).
Proof.
  eapply SOS_again.
  { cbv.  apply SOS_While. }
    eapply SOS_again.
  { apply SOS_If_true. cbn.  reflexivity. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { apply SOS_Seqf. apply SOS_Assign. }
   eapply SOS_stop.
Qed.

(* 13.c) L'énoncé signifie que lorsque qu'on exécute le programme Pcarre_2 en partant de *)
(*       l'état [I = 1 ; X = 1 ; Y = 3], on arrive à une configuration intermédiaire où Pcarre_2 peut être exécuté *)
(*       en partant de l'état [I = 2 ; X = 4; Y = 5] *)

Lemma SOS_Pcarre_2_2e_tour : SOS (Inter Pcarre_2 [1; 1; 3]) (Inter Pcarre_2 [2; 4; 5]).
Proof.
  eapply SOS_again.

  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  { cbv.  apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. apply SOS_Assign. }
  cbn.  apply SOS_stop.
Qed.

(* 13.d) L'énoncé signifie que lorsque qu'on exécute le programme Pcarre_2 en partant de *)
(*       l'état [i = 2 ; x = 4 ; y = 5], on arrive à une configuration finale avec un état inchangé *)

Theorem SOS_Pcarre_2_fini : SOS (Inter Pcarre_2 [2; 4; 5]) (Final [2; 4; 5]).
Proof.
    eapply SOS_again.
  { cbv.  apply SOS_While. }
    eapply SOS_again.
  { apply SOS_If_false. cbn.  reflexivity. }
  eapply SOS_again.
  { apply SOS_Skip. }
  eapply SOS_stop.
Qed.

(* 13.e) *)

Theorem SOS_Pcarre_2_fin_V1 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  apply SOS_trans with (Inter Pcarre_2 [1; 1; 3]).
  apply SOS_Pcarre_2_1er_tour.
  apply SOS_trans with (Inter Pcarre_2 [2; 4; 5]).
  apply SOS_Pcarre_2_2e_tour.
  apply SOS_Pcarre_2_fini.
Qed.

(* 14.a) *)

(** On a besoin de deux lemmes arithmétiques, démontrables avec la tactique ring. *)

Lemma Sn_2 n : S n + S n = S (S (n + n)).
Proof. ring. Qed.

Lemma Sn_carre n : S n * S n = S (n + n + n * n).
Proof. ring. Qed.

Definition invar_cc n := [n; n*n; S (n+n)].

(* L'énoncé signifie que pour un entier naturel n donné, lorsque qu'on exécute le programme corps_carre avec pour état de départ  *)
(* [I = n ; X = n*n ; Y = S (n+n)] on arrive à une config finale avec pour état *)
(* [I = S(n) ; X = S(n)*S(n) ; Y = S (S(n) + S(n))] *)

Theorem SOS_corps_carre n : SOS (Inter corps_carre (invar_cc n)) (Final (invar_cc (S n))).
Proof.
  eapply SOS_again.
  { cbv[corps_carre]. apply SOS_Seqf. cbv[invar_cc]. cbv[incrI]. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. cbn. cbv[incrX]. apply SOS_Assign. }
  cbn.
  eapply SOS_again.
  { apply SOS_Assign. }
  cbn.
  rewrite <- Sn_2.
  rewrite <- Sn_carre.
  cbv[invar_cc].
  apply SOS_stop.
Qed.

(* 14.b) L'énoncé signifie que pour un entier naturel n et une expression Winstr i donnés *)
(*       lorsque qu'on exécute le programme corps_carre suivi de i en partant de *)
(*       l'état [I = n ; X = n*n ; Y = S (n+n)], on arrive à une configuration intermédiaire où le programme peut être exécuté *)
(*       en partant de l'état [I = 2 ; X = 4; Y = 5] *)

Lemma SOS_corps_carre_inter n i :
  SOS (Inter (Seq corps_carre i) (invar_cc n)) (Inter i (invar_cc (S n))).
Proof.
  eapply SOS_again.
  { cbv[corps_carre]. apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. cbn. apply SOS_Assign. }
  cbn.
  eapply SOS_again.
  { apply SOS_Seqf. apply SOS_Assign. }
  cbn.
  rewrite <- Sn_carre.
  rewrite <- Sn_2.
  apply SOS_stop.
Qed.

(* 14.c) *)
(* L'énoncé signifie que pour tous entiers naturels n et i, si n et i sont différents alors *)
(* lorsque qu'on exécute le programme Pcarre en partant de *)
(* l'état [I = i; X = i * i; Y = S (i + i)], on arrive à une configuration intermédiaire où le programme peut être exécuté en partant de l'état [I = S i; X = S i * S i; Y = S (S i + S i)] *)

Lemma SOS_Pcarre_tour :
  forall n i, eqnatb i n = false ->
  SOS (Inter (Pcarre n) (invar_cc i)) (Inter (Pcarre n) (invar_cc (S i))).
Proof.
  intros.
  eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. cbn. rewrite H. cbn. reflexivity. }
  eapply SOS_again.
  { apply SOS_Seqi. cbv[corps_carre]. apply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. cbn. apply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { cbn. apply SOS_Seqf. apply SOS_Assign. }
  cbn.
  rewrite <- Sn_carre.
  rewrite <- Sn_2.
  apply SOS_stop.
Qed.

(* 14.d) *)

Lemma eqnatb_refl : forall n, eqnatb n n = true.
Proof.
  intros.
  induction n as [ | ].
  - reflexivity.
  - apply IHn.
Qed.

(* L'énoncé signifie que pour tout entier naturel n, *)
(* lorsque qu'on exécute le programme Pcarre en partant de *)
(* l'état [I = n; X = n * n; Y = S (n + n)], on arrive à une configuration finale avec un *)
(* état identique *)

Theorem SOS_Pcarre_n_fini : forall n, SOS (Inter (Pcarre n) (invar_cc n)) (Final (invar_cc n)).
Proof.
  intros.
  eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_false. cbn. rewrite eqnatb_refl. cbn. reflexivity. }
  eapply SOS_again.
  { apply SOS_Skip. }
  apply SOS_stop.
Qed.

(* 14.e) *)
(* On utilise la transitivité de SOS afin de raccourcir la preuve.
   On doit prouver la passage de  *)
Theorem SOS_Pcarre_2_fin_V2 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  eapply SOS_trans.
  { apply SOS_Pcarre_tour. reflexivity. } (* l'état est invar_cc 0. 0 != 2, donc on peut utiliser le 
                                             lemme SOS_Pcarre_tour pour prouver qu'un tour de boucle
                                             de Pcarre_2 en partant de l'état invar_cc 0 va dans la 
                                             configuration interlmédiaire où l'état est invar_cc 1 *)
  eapply SOS_trans.
  { apply SOS_Pcarre_tour. reflexivity. } (* de même, on utilise le lemme pour prouver le passage à la
                                             configuration où l'état est invar_cc 2*)
  eapply SOS_trans.
  { apply SOS_Pcarre_n_fini. } (* ici, on a l'état invar_cc 2 et Pcarre_2, donc on utilise le théorème
                                  SOS_Pcarre_n_fini *)
  apply SOS_stop.
Qed.

(* 14.f)  *)
(* L'énoncé signifie que pour tout entier naturel i, 
lorsque qu'on exécute le programme Pcarre_inf en partant de 
l'état [I = i; X = i * i; Y = S (i + i)], on arrive à une configuration intermédiaire avec 
l'état [I = S(i); X = S(i) * S(i); Y = S (S(i) + S(i))] *)

Lemma SOS_Pcarre_inf_tour :
  forall i,
  SOS (Inter Pcarre_inf (invar_cc i)) (Inter Pcarre_inf (invar_cc (S i))).
Proof.
  intros.
  eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  { cbv[corps_carre]. apply SOS_Seqi. cbv[corps_carre]. apply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. apply SOS_Assign. }
  cbn.
  rewrite <- Sn_carre.
  rewrite <- Sn_2.
  apply SOS_stop.
Qed.

(* 14.e) *)
(* L'énoncé signifie que pour tout entier naturel i, si on exécute le programme Pcarre_inf en
partant de l'état invar_cc 0, on peut arriver dans une configuration intermédiaire
avec pour état invar_cc i*)

Theorem SOS_Pcarre_inf_n :
  forall i,
  SOS (Inter Pcarre_inf [0; 0; 1]) (Inter Pcarre_inf (invar_cc i)).
Proof.
  intros.
  induction i as [ | ].
  - cbv[invar_cc]. cbn. apply SOS_stop.
  - eapply SOS_trans.
    -- apply IHi.
    -- apply SOS_Pcarre_inf_tour.
Qed.


(* 15.a) *)
Fixpoint f_SOS_1 (i : Winstr) (s : state) : config :=
  match i with
  | Skip => Final s
  | Assign n a => Final (update s n (evalA a s))
  | Seq w1 w2 => match f_SOS_1 w1 s with
                  | Inter w1' s' => Inter (Seq w1' w2) s'
                  | Final s' => Inter w2 s'
                  end
  | If be w1 w2 => match evalB be s with
                   | true => Inter w1 s
                   | false => Inter w2 s
                   end
  | While be w => Inter (If be (Seq w (While be w)) Skip) s
  end.

(* 15.b) *)
Lemma f_SOS_1_corr : forall i s, SOS_1 i s (f_SOS_1 i s).
Proof.
  intros.
  induction i.
  - apply SOS_Skip.
  - apply SOS_Assign.
  - cbn. destruct (f_SOS_1 i1 s).
    -- apply SOS_Seqi. apply IHi1.
    -- apply SOS_Seqf. apply IHi1.
  - case_eq (evalB b s).
    -- intro. cbn. rewrite H. apply SOS_If_true. apply H.
    -- intro. cbn. rewrite H. apply SOS_If_false. apply H.
  - cbn. apply SOS_While.
Qed.

(* Programmes "restants à éxecuter" *)
Definition If_instr := If (Bnot (Beqnat Ir (Aco 2))) (Seq corps_carre (While (Bnot (Beqnat Ir (Aco 2))) corps_carre)) Skip.
Definition Seq_instr := Seq corps_carre (While (Bnot (Beqnat Ir (Aco 2))) corps_carre).
Definition Seq_instr_2 := Seq (Seq incrX incrY) (While (Bnot (Beqnat Ir (Aco 2))) corps_carre).
Definition Seq_instr_3 := Seq incrY (While (Bnot (Beqnat Ir (Aco 2))) corps_carre).

Lemma SOS_Pcarre_2_1er_tour_v2 : SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  apply SOS_again with (f_SOS_1 Pcarre_2 [0;0;1]).
  apply f_SOS_1_corr.
  apply SOS_again with (f_SOS_1 If_instr [0;0;1]).
  apply f_SOS_1_corr.
  apply SOS_again with (f_SOS_1 Seq_instr [0;0;1]).
  apply f_SOS_1_corr.
  apply SOS_again with (f_SOS_1 Seq_instr_2 [1;0;1]).
  apply f_SOS_1_corr.
  apply SOS_again with (f_SOS_1 Seq_instr_3 [1;1;1]).
  apply f_SOS_1_corr.
  apply SOS_stop.
Qed.






















