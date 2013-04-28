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

Add LoadPath "../basis". 
Add LoadPath "../list_extensions". 
Add LoadPath "../term_algebra". 
Add LoadPath "../term_orderings". 

Require Import Arith.
Require Import List.
Require Import Relations.
Require Import term.
Require Import rpo.

Module  Ord_sig <: Signature.

Inductive symb0 : Set := nat_O | nat_S | ord_zero | ord_cons.

Definition symb := symb0.

Lemma eq_symbol_dec : forall f1 f2 : symb, {f1 = f2} + {f1 <> f2}.
Proof.
intros; decide equality.
Qed.

(** The arity of a symbol contains also the information about built-in theories as in CiME *)
Inductive arity_type : Set :=
  | AC : arity_type
  | C : arity_type
  | Free : nat -> arity_type.

Definition arity : symb -> arity_type :=
  fun f => match f with
	          | nat_O => Free 0
                  | nat_S => Free 1
                  | ord_zero => Free 0
                  | ord_cons => Free 3
                  end.

End Ord_sig.

(** * Module Type Variables. 
 There are almost no assumptions, except a decidable equality. *) 
Module Vars <: Variables.

Definition var := nat.

Lemma eq_variable_dec : forall v1 v2 : var, {v1 = v2} + {v1 <> v2}.
Proof.
intros; decide equality.
Qed.

End Vars.

Module  Ord_prec <: Precedence.

Definition A : Set := Ord_sig.symb.
Import Ord_sig.

Definition prec : relation A :=
   fun f g => match f, g with
                      | nat_O, nat_S => True
                      | ord_zero, ord_cons => True
                      | nat_O, ord_cons => True
                      | nat_S, ord_cons => True
                      | _, _ => False
                      end.

Inductive status_type : Set :=
  | Lex : status_type
  | Mul : status_type.

Definition status : A -> status_type := fun f => Lex.

Lemma prec_dec : forall a1 a2 : A, {prec a1 a2} + {~ prec a1 a2}.
Proof.
intros a1 a2; destruct a1; destruct a2.
right; intro; contradiction.
left; simpl; trivial.
right; intro; contradiction.
left; simpl; trivial.
right; intro; contradiction.
right; intro; contradiction.
right; intro; contradiction.
left; simpl; trivial.
right; intro; contradiction.
right; intro; contradiction.
right; intro; contradiction.
left; simpl; trivial.
right; intro; contradiction.
right; intro; contradiction.
right; intro; contradiction.
right; intro; contradiction.
Qed.

Lemma prec_antisym : forall s, prec s s -> False.
Proof.
intros s; destruct s; simpl; trivial.
Qed.

Lemma prec_transitive : transitive A prec.
Proof.
intros s1 s2 s3; destruct s1; destruct s2; destruct s3; simpl; intros; trivial; contradiction.
Qed.

End Ord_prec.

Module Ord_alg <: Term := term.Make (Ord_sig) (Vars).
Module Ord_rpo <: RPO := rpo.Make (Ord_alg) (Ord_prec).

Import Ord_alg.
Import Ord_rpo.
Import Ord_sig.

Fixpoint nat_translation (n : nat) :  term :=
  match n with
                   | O => Term nat_O nil
                   | S n => Term nat_S ((nat_translation n) :: nil)
                   end.

Inductive T1 : Set :=
  zero : T1
| cons : T1 -> nat -> T1 -> T1.

Fixpoint translation (o : T1) : term :=
  match o with
                  | zero => Term ord_zero nil
                  | cons o1 n o2 =>
                          Term ord_cons ((translation o1) :: (nat_translation n) :: (translation o2) :: nil)
                  end.

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

Lemma lt_trans : forall o1 o2 o3, o1 < o2 -> o2 < o3 -> o1 < o3.
Proof.
induction o1 as [ | a1 IHa1 n1 b1 IHb1].
do 2 inversion 1; try apply zero_lt.
inversion 1 as [ | a1' a2 | a1' n1' n2 | H1 H2 H3 b2].
inversion 1; apply head_lt; [ apply IHa1 with a2 | idtac | idtac ]; trivial.
inversion 1;
 [ apply head_lt | apply coeff_lt; apply Lt.lt_trans with n2 | apply coeff_lt] ; trivial.
subst; inversion 1;
 [apply head_lt | apply coeff_lt | apply tail_lt; apply IHb1 with b2] ; trivial.
Qed.

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

(* inversion lemmas *)

Lemma nf_inv1 : forall a n b, nf (cons a n b) -> nf a.
Proof.
  inversion_clear 1; auto.
Qed.

Lemma nf_inv2 : forall a n b, nf (cons a n b) -> nf b.
Proof.
 inversion_clear 1; auto  with T1.
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


Theorem lt_nat_inc_rpo : 
  forall n n', (n < n')%nat -> rpo (nat_translation n) (nat_translation n').
Proof.
intro n; induction n as [ | n]; intros [ | n'].
intro Abs; absurd ((0 < 0)%nat); trivial; auto with arith.
intros _; simpl; apply Top_gt; simpl; trivial; contradiction.
intro Abs; absurd ((S n < 0)%nat); trivial; auto with arith. 
intro H; assert (H' := lt_S_n _ _ H). 
simpl; apply Top_eq_lex; trivial.
apply List_gt; trivial; apply IHn; trivial.
intros s [s_eq_transl_n | s_in_nil]; [subst s | contradiction].
apply Subterm with (nat_translation n').
left; trivial.
apply Lt; apply IHn; trivial.
Qed.

Theorem rpo_nat_ord :
  forall n o1 p o2, rpo (nat_translation n) (translation (cons o1 p o2)).
Proof.
intro m; simpl; induction m as [ | m].
simpl; intros o1 p o2; apply Top_gt; simpl; trivial; contradiction.
simpl; intros o1 p o2; apply Top_gt; simpl; trivial.
intros s [s_eq_transl_m | s_in_nil]; [idtac | contradiction].
subst s; apply IHm.
Qed.

Fixpoint size (o:T1):nat :=
 match o with zero => 0
            | cons a n b => S (size a + n + size b)%nat
         end.

Lemma size2 : forall a n b , (size a < size (cons a n b))%nat.
Proof.
 simpl; auto with arith.
Qed.

Lemma size3 : forall a n b , (size b < size (cons a n b))%nat.
Proof.
 simpl; auto with arith.
Qed.

Theorem lt_inc_rpo : 
    forall n,  forall o' o, (size o + size o' <= n)%nat->
                              (o < o')%ca -> nf o -> nf o' -> 
                                  rpo (translation o) (translation o').
Proof.
intro m; induction m as [ | m].
destruct o' as [ | o1' n' o2'].
inversion 2.
destruct o as [ | o1 n o2]; inversion 1.
destruct o' as [ | o1' n' o2'].
destruct o as [ | o1 n o2]; inversion 2.
destruct o as [ | o1 n o2].
intros _ _ _ _; simpl; apply Top_gt; [simpl; trivial | intros; contradiction].
intros Size o_lt_o' nf_o nf_o'; simpl.
apply Top_eq_lex; trivial.
inversion o_lt_o'; subst. (* 4 cases *)
(* o1 < o1' /\ cons o1 n o2 < cons o1' n' o2' *)
apply List_gt; trivial; apply IHm; trivial.
apply  lt_n_Sm_le.
apply Lt.lt_le_trans with (size (cons o1 n o2) + size (cons o1' n' o2'))%nat.
apply plus_lt_compat; apply size2.
trivial.
apply nf_inv1 with n o2; trivial.
apply nf_inv1 with n' o2'; trivial.
(* o1 = o1' /\ n < n' /\ cons o1 n o2 < cons o1' n' o2' *)
apply List_eq; apply List_gt; trivial.
apply lt_nat_inc_rpo; trivial.
(* o1 = o1' /\ n = n' /\ o2 < o2' /\ cons o1 n o2 < cons o1' n' o2' *)
do 2 apply List_eq; apply List_gt; trivial; apply IHm.
apply  lt_n_Sm_le.
apply Lt.lt_le_trans with (size (cons o1' n' o2) + size (cons o1' n' o2'))%nat.
apply plus_lt_compat; apply size3.
trivial.
trivial.
apply nf_inv2 with o1' n'; trivial.
apply nf_inv2 with o1' n'; trivial.
inversion o_lt_o'; subst. (* 4 cases *)
(* o1 < o1' /\ cons o1 n o2 < cons o1' n' o2' *)
intros s [s_eq_transl_o1 | [s_eq_transl_n | [s_eq_transl_o2 | s_in_nil]]]. 
(* o1 < cons o1' n' o2' *)
subst s; apply Subterm with (translation o1').
left; trivial.
apply Lt; apply IHm; trivial.
apply  lt_n_Sm_le.
apply Lt.lt_le_trans with (size (cons o1 n o2) + size (cons o1' n' o2'))%nat.
apply plus_lt_compat; apply size2.
trivial.
apply nf_inv1 with n o2; trivial.
apply nf_inv1 with n' o2'; trivial.
(* n < cons o1' n' o2' *)
subst s; refine (rpo_nat_ord n o1' n' o2').
(* o2 < cons o1' n' o2' *)
subst s; apply (IHm (cons o1' n' o2') o2).
apply  lt_n_Sm_le.
apply Lt.lt_le_trans with (size (cons o1 n o2) + size (cons o1' n' o2'))%nat.
apply plus_lt_le_compat; [apply size3 | apply le_n].
trivial.
apply lt_trans with (cons o1 n o2); trivial; apply tail_lt_cons; trivial.
apply nf_inv2 with o1 n; trivial.
trivial.
contradiction.
(* o1 = o1' /\ n < n' /\ cons o1 n o2 < cons o1' n' o2' *)
intros s [s_eq_transl_o1 | [s_eq_transl_n | [s_eq_transl_o2 | s_in_nil]]]. 
(* o1 < cons o1' n' o2' *)
subst s; apply Subterm with (translation o1').
left; trivial.
apply Eq; trivial.
(* n < cons o1' n' o2' *)
subst s; refine (rpo_nat_ord n o1' n' o2').
(* o2 < cons o1' n' o2' *)
subst s; apply (IHm (cons o1' n' o2') o2).
apply  lt_n_Sm_le.
apply Lt.lt_le_trans with (size (cons o1' n o2) + size (cons o1' n' o2'))%nat.
apply plus_lt_le_compat; [apply size3 | apply le_n].
trivial.
apply lt_trans with (cons o1' n o2); trivial; apply tail_lt_cons; trivial.
apply nf_inv2 with o1' n; trivial.
trivial.
contradiction.
(* o1 = o1' /\ n = n' /\ o2 < o2' /\ cons o1 n o2 < cons o1' n' o2' *)
intros s [s_eq_transl_o1 | [s_eq_transl_n | [s_eq_transl_o2 | s_in_nil]]]. 
(* o1 < cons o1' n' o2' *)
subst s; apply Subterm with (translation o1').
left; trivial.
apply Eq; trivial.
(* n < cons o1' n' o2' *)
subst s; refine (rpo_nat_ord n' o1' n' o2').
(* o2 < cons o1' n' o2' *)
subst s; apply (IHm (cons o1' n' o2') o2).
apply  lt_n_Sm_le.
apply Lt.lt_le_trans with (size (cons o1' n' o2) + size (cons o1' n' o2'))%nat.
apply plus_lt_le_compat; [apply size3 | apply le_n].
trivial.
apply lt_trans with (cons o1' n' o2); trivial; apply tail_lt_cons; trivial.
apply nf_inv2 with o1' n'; trivial.
trivial.
contradiction.
Qed.

