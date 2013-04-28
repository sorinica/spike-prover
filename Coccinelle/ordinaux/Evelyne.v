(**************************************************************************)
(*           *                                                            *)
(*     _     *   The Coccinelle Library / Evelyne Contejean               *)
(*    <o>    *          CNRS-LRI-Universite Paris Sud                     *)
(*  -/@|@\-  *                   A3PAT Project                            *)
(*  -@ | @-  *                                                            *)
(*  -\@|@/-  *      This file is distributed under the terms of the       *)
(*    -v-    *      CeCILL-C licence                                      *)
(*           *                                                            *)
(**************************************************************************)

Require Import Arith.
Require Import Omega. (* ( :-) *)
Require Import Compare_dec.
Require Import Relations.
Require Import AccP. 
Require Import Wellfounded.


Inductive T1 : Set :=
  zero : T1
| cons : T1 -> nat -> T1 -> T1.

Inductive lt : T1 -> T1 -> Prop :=
|  zero_lt : forall a n b, lt zero  (cons a n b)
|  head_lt :
    forall a a' n n' b b', lt a a' ->
                           lt (cons a n b) (cons a' n' b')
|  coeff_lt : forall a n n' b b', (n < n')%nat ->
                                 lt (cons a n b) (cons a n' b')
|  tail_lt : forall a n b b', lt b b' ->
                                 lt (cons a n b)  (cons a n b')
where  "o < o'" := (lt o o') : cantor_scope.

Hint Resolve zero_lt head_lt coeff_lt tail_lt : T1.

Open Scope cantor_scope.

Delimit Scope cantor_scope with ca.


Definition le (alpha beta :T1) := alpha = beta \/ alpha < beta.
Notation "alpha <= beta" := (le alpha beta) : cantor_scope.

Hint Unfold le : T1.


(* The real Cantor normal form needs the exponents of omega to be
   in strict decreasing order *)


Inductive nf : T1 -> Prop :=
| zero_nf : nf zero
| single_nf : forall a n, nf a ->  nf (cons a n zero)
| cons_nf : forall a n a' n' b, a' < a ->
                             nf a ->
                             nf(cons a' n' b)->
                             nf(cons a n (cons a' n' b)).
Hint Resolve zero_nf single_nf cons_nf : T1.

Lemma lt_trans : forall a b c, a < b -> b < c -> a  < c.
Admitted.

Lemma le_lt_trans : forall a b c, a <= b -> b < c -> a  < c.
Admitted.

Lemma lt_le_trans : forall a b c, a < b -> b <= c -> a  < c.
Admitted.


(* inversion lemmas *)


Lemma nf_inv1 : forall a n b, nf (cons a n b) -> nf a.
Proof.
  inversion_clear 1; auto.
Qed.

Lemma nf_inv2 : forall a n b, nf (cons a n b) -> nf b.
Proof.
 inversion_clear 1; auto  with T1.
Qed.

Hint Resolve nf_inv1 nf_inv2 : T1.

Ltac nf_inv := (eapply nf_inv1; progress eauto)||
               (eapply nf_inv2; progress eauto).

Lemma nf_tail_lt_nf : forall  b b', b' < b -> nf b' ->
                          forall a n,   nf (cons a n b) ->
                                        nf (cons a n b').
Proof.
 induction 1.
 constructor; eauto with T1.
 constructor.
 apply lt_trans with a'; auto.
 inversion H1; eauto with T1.
 eauto with T1.
 assumption.
 constructor.
 inversion H1;eauto with T1.
 eauto with T1.
 assumption.
 constructor.
 inversion H1;eauto with T1.
 eauto with T1.
 assumption.
Qed.


Lemma tail_lt_cons : forall b n a,
     nf (cons a n b)->
     b < cons a n b.
Proof.
 induction b.
 constructor.
 constructor 2.
 inversion H;auto.
Qed.







(* we define a mono-sorted tree algebra for T1 *)

Inductive xtree : Set :=
 nat_O : xtree
|nat_S : xtree -> xtree
|ord_zero : xtree
|ord_cons : xtree -> xtree -> xtree -> xtree.


Inductive is_nat : xtree -> Prop :=
  is_nat_O : is_nat nat_O
| is_nat_S : forall x, is_nat x -> is_nat (nat_S x).

Inductive nat_lt : xtree -> xtree -> Prop :=
 nat_lt_O : forall x, nat_lt nat_O (nat_S x)
|nat_lt_S : forall x y, nat_lt x y -> nat_lt (nat_S x) (nat_S y).

Fixpoint nat_x (n:nat) : xtree :=
  match n with
    0 => nat_O
  | S p => nat_S (nat_x p)
  end.

Lemma is_nat_ok : forall n, is_nat (nat_x n).
 induction n;simpl;constructor;auto.
Qed.
Hint Resolve is_nat_ok.

(* forget type *)

Fixpoint cpnf_x (c:T1) : xtree := 
match c with
 zero => ord_zero
|cons a n b => ord_cons (cpnf_x a) (nat_x n) (cpnf_x b)
end.

Fixpoint size (o:T1):nat :=
 match o with zero => 0
            | cons a n b => S (size a + n + size b)%nat
         end.

Lemma size1 : forall a n b, (size zero < size (cons a n b))%nat.
Proof.
 simpl.
 intros.
 auto with arith.
Qed.

Lemma size2 : forall a n b , (size a < size (cons a n b))%nat.
Proof.
 simpl; auto with arith.
Qed.

Lemma size3 : forall a n b , (size b < size (cons a n b))%nat.
Proof.
 simpl; auto with arith.
Qed.

Hint Resolve size2 size3.

Lemma lt_subterm1 : forall a a'  n'  b', a < a' ->
                                         a < cons a' n' b'.
Proof.
Admitted.

Lemma lt_subterm2 : forall a a' n n' b b', a < a' ->
                                           nf (cons a n  b) ->
                                           nf (cons a' n' b') ->
                                           b < cons a' n' b'.
Proof.
Admitted.


Inductive lpo : xtree -> xtree -> Prop :=
(* subterm rules *)

|  lpo_S1 : forall x, lpo x (nat_S x) 
|  lpo_S2 : forall x y, lpo x y -> lpo x (nat_S y)
|  lpo_cons_a1 : forall a n b, lpo a (ord_cons  a n b)
|  lpo_cons_a2 : forall a a' n b, lpo a a' -> lpo a (ord_cons  a' n b)
|  lpo_cons_n1 : forall a n b, lpo n (ord_cons  a n b)
|  lpo_cons_n2 : forall a  n n' b, lpo n n' -> lpo n (ord_cons  a n' b)
|  lpo_cons_b1 : forall a n b, lpo b (ord_cons  a n b)
|  lpo_cons_b2 : forall a n b b', lpo b b' -> lpo b (ord_cons  a n b')

(* precedence rules *)
|  lpo_0_S : forall i, lpo nat_O (nat_S i)
|  lpo_0_cons : forall a n b, lpo ord_zero (ord_cons a n b)
|  lpo_0_cons2 : forall a n b, lpo nat_O (ord_cons a n b)
|  lpo_S_cons : forall p a n b, lpo p (ord_cons a n b) ->
                                lpo (nat_S p) (ord_cons a n b)


(* lexicographic rules *)

| lpo_SS : forall n p,  lpo n (nat_S p) -> lpo n p -> lpo (nat_S n) (nat_S p)

| lpo_CC1 : forall a0 a n0 n b0 b, lpo a0 (ord_cons a n b) -> 
                                   lpo n0 (ord_cons a n b) -> 
                                   lpo b0 (ord_cons a n b) -> 
                             lpo a0 a ->
                             lpo (ord_cons a0 n0 b0) (ord_cons a n b)

| lpo_CC2 : forall a n0 n b0 b, lpo a (ord_cons a n b) -> 
                                   lpo n0 (ord_cons a n b) -> 
                                   lpo b0 (ord_cons a n b) -> 
                                   lpo n0 n ->
                             lpo (ord_cons a n0 b0) (ord_cons a n b)


| lpo_CC3 : forall a n b0 b, lpo a (ord_cons a n b) -> 
                                   lpo n (ord_cons a n b) -> 
                                   lpo b0 (ord_cons a n b) -> 
                                   lpo b0 b ->
                             lpo (ord_cons a n b0) (ord_cons a n b).

 Hint Constructors lpo.


Theorem lpo_trans : forall t t1 t2, lpo t t1 -> lpo t1 t2 -> lpo t t2.
Admitted.


Lemma nat_lt_ord : forall n a p b, is_nat n -> lpo n (ord_cons a p b).
 induction n;simpl;auto.
 intros.
 apply lpo_S_cons.
 apply IHn.
 inversion H;auto.
 intros.
 inversion H.
Qed.
Hint Resolve nat_lt_ord.
Hint Resolve lt_subterm2 lt_subterm1. 

Theorem lt_inc_lpo_0 : forall n, 
                           forall o' o, (size o + size o' <= n)%nat->
                              o < o' -> nf o -> nf o' -> 
                                  lpo (cpnf_x o) (cpnf_x o').
 induction n.
  destruct o'.
  inversion 2.
 destruct o.
 simpl.
 inversion 1.
 simpl;inversion 1.
 inversion 2.
 simpl.
 intros; apply lpo_0_cons.
 simpl; intros; apply lpo_CC1.
 change (lpo (cpnf_x a) (cpnf_x (cons a' n' b'))).
 apply IHn.
 subst o;subst o'.
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (size (cons a n0 b) + size (cons a' n' b'))%nat.
 Hint Resolve size2.
 auto with arith.
 auto.
 eapply lt_subterm1;auto.
 nf_inv.
 auto.
 auto.
 simpl.
 change (lpo (cpnf_x b) (cpnf_x (cons a' n' b'))).
 apply IHn;auto.
 subst o;subst o'.
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (size (cons a n0 b) + size (cons a' n' b'))%nat.
 auto with arith.
 auto.
 eauto.
 nf_inv.
 apply IHn.
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (size (cons a n0 b) + size (cons a' n' b'))%nat.
 apply plus_lt_compat;auto.
 subst o;subst o';auto. 
 auto.
 nf_inv.
 nf_inv.
 simpl;intros.
 apply lpo_CC2;auto.
  change (lpo  (cpnf_x b) (cpnf_x (cons a n' b'))).
 apply IHn.
 subst o;subst o'.
 apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (size (cons a n0 b) + size (cons a n' b'))%nat.
 auto with arith.
 auto.
 apply lt_le_trans with (cons a n0 b).
 apply tail_lt_cons;auto.
 right;auto with T1.
 nf_inv.
 auto.
  elim H1.
 simpl;auto.
 simpl;intros.
 apply lpo_trans with (nat_x m);auto.
 simpl;auto.
 intros.
 apply lpo_CC3;auto.
 change  (lpo (cpnf_x b) (cpnf_x (cons a n0 b'))).
 apply IHn.
 subst o;subst o'.
apply  lt_n_Sm_le .
 apply Lt.lt_le_trans with (size (cons a n0 b) + size (cons a n0 b'))%nat.
 auto with arith.
 auto.
 apply lt_le_trans with (cons a n0 b).
 apply tail_lt_cons;auto.
 right;auto with T1.
 nf_inv.
 auto.
 apply IHn.
 apply  lt_n_Sm_le .
 subst o;subst o'.
 apply Lt.lt_le_trans with (size (cons a n0 b) + size (cons a n0 b'))%nat.
 apply plus_lt_compat;auto.
 auto.
 auto.
 nf_inv.
 nf_inv.
Qed.
 

Theorem well_founded_lpo : well_founded lpo.
Proof.
 Admitted.


Section  well_founded.
 
  Let R := restrict T1 nf lt.

  Hint Unfold restrict R.

 Lemma R_inc_lpo : forall o o', R o o' -> lpo (cpnf_x o) (cpnf_x o').
 Proof.
  intros o o' (H,(H1,H2)).
  eapply lt_inc_lpo_0;auto.
 Qed. 

 
 Lemma nf_Wf : well_founded_P _ nf lt.
Proof.
 unfold well_founded_P.
 intros.
 unfold restrict.
 generalize (Acc_inverse_image _ _ lpo cpnf_x a (well_founded_lpo (cpnf_x a))).
  intro.
 eapply  Acc_incl  with  (fun x y : T1 => lpo (cpnf_x x) (cpnf_x y)). 
 red.
 apply R_inc_lpo.
 auto.
Qed.


End well_founded.


 