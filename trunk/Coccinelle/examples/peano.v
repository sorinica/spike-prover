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

Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/basis".
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/list_extensions". 
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/term_algebra". 
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/term_orderings". 

Require Import List.
Require Import Relations.
Require Import term.
Require Import rpo.

Require Import term_spec.

Module  Peano_sig <: Signature.

Inductive symb0 : Set := zero | succ | plus.

Module Symb.
Definition A := symb0.

Lemma eq_dec : forall f1 f2 : A, {f1 = f2} + {f1 <> f2}.
Proof.
intros; decide equality.
Qed.
End Symb.
(** The arity of a symbol contains also the information about built-in theories as in CiME *)


Definition arity : Symb.A -> arity_type :=
  fun f => match f with
                  | zero => Free 0
                  | succ => Free 1
                  | plus => Free 2
                  end.

End Peano_sig.

(** * Module Type Variables. 
 There are almost no assumptions, except a decidable equality. *) 
Module Vars.

Definition A := nat.

Lemma eq_dec : forall v1 v2 : A, {v1 = v2} + {v1 <> v2}.
Proof.
intros; decide equality.
Qed.

End Vars.

Module  Peano_prec <: Precedence.

Definition A : Set := Peano_sig.Symb.A.
Import Peano_sig.

Definition prec : relation A :=
   fun f g => match f, g with
                      | zero, succ => True
                      | zero, plus => True
                      | succ, plus => True
                      | _, _ => False
                      end.

Definition status : A -> status_type := fun f => Lex.

Lemma prec_dec : forall a1 a2 : A, {prec a1 a2} + {~ prec a1 a2}.
Proof.
intros a1 a2; destruct a1; destruct a2.
right; intro; contradiction.
left; simpl; trivial.
left; simpl; trivial.
right; intro; contradiction.
right; intro; contradiction.
left; simpl; trivial.
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

End Peano_prec.

Module Peano_alg <: Term := term.Make (Peano_sig) (Vars).
Module Peano_rpo <: RPO := rpo.Make (Peano_alg) (Peano_prec).

Import Peano_alg.
Import Peano_rpo.
Import Peano_sig.

Lemma peano_wf1 :
  forall x : term, rpo x (Term plus (x :: (Term zero nil) :: nil)).
Proof. 
intros; apply (Subterm plus (x :: (Term zero nil) :: nil) x x).
left; trivial.
apply Equiv; apply Eq.
Qed.

Lemma peano_wf2 :
  forall x y : term, rpo (Term succ ((Term plus (x :: y :: nil)) :: nil))
                                   (Term plus (x :: (Term succ (y :: nil)) :: nil)).
Proof.
intros x y; apply Top_gt.
simpl; trivial.
intros s' [s'_eq_x_plus_y | s'_in_nil]; [subst s' | contradiction].
apply Top_eq_lex.
trivial.
apply List_eq; [apply Eq | apply List_gt]; trivial.
apply (Subterm succ (y :: nil) y y); [left; trivial | apply Equiv; apply Eq].
intros s' [s'_eq_x | [s'_eq_y | s'_in_nil]].
subst s'; apply (Subterm plus (x :: Term succ (y :: nil) :: nil) x x); [left; trivial | apply Equiv; apply Eq].
subst s'; apply (Subterm plus (x :: Term succ (y :: nil) :: nil) y (Term succ (y :: nil))).
right; left; trivial.
apply Lt; apply (Subterm succ (y :: nil) y y); [left; trivial | apply Equiv; apply Eq].
contradiction.
Qed.
