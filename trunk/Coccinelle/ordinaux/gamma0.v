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

Inductive symb0 : Set := nat_O | nat_S | ord_zero | ord_cons | ord_psi.

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
                  | ord_psi => Free 2
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
                      | nat_O, ord_psi => True
                      | nat_S, ord_psi => True
                      | ord_zero, ord_psi => True
                      | ord_cons, ord_psi => True
                      | _, _ => False
                      end.

Inductive status_type : Set :=
  | Lex : status_type
  | Mul : status_type.

Definition status : A -> status_type := fun f => Lex.
                    
Lemma prec_dec : forall a1 a2 : A, {prec a1 a2} + {~ prec a1 a2}.
Proof.
intros a1 a2; destruct a1; destruct a2;
try (( right; intro; contradiction) || (left; simpl; trivial)).
Qed.

Lemma prec_antisym : forall s, prec s s -> False.
Proof.
intros s; destruct s; simpl; trivial.
Qed.

Lemma prec_transitive : transitive A prec.
Proof.
intros s1 s2 s3; destruct s1; destruct s2; destruct s3;
simpl; intros; trivial; contradiction.
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

Inductive T2 : Set :=
  zero : T2
| cons : T2 -> T2 -> nat -> T2 -> T2.

Definition psi alpha beta  := cons alpha beta  0 zero.

Definition one  := psi zero zero.

Fixpoint translation (o : T2) : term :=
  match o with
                  | zero => Term ord_zero nil
                  | cons o1 o2 0 zero => 
                          Term ord_psi ((translation o1) :: (translation o2) :: nil)
                  | cons o1 o2 n o3 =>
                          Term ord_cons 
	                                ((Term ord_psi ((translation o1) :: (translation o2) :: nil)) ::
                                                  (nat_translation n) :: (translation o3) :: nil)
                  end.

Inductive lt : T2 -> T2 -> Prop :=
| (* 1 *) 
 lt_1 : forall alpha beta n gamma,  lt zero (cons alpha beta n gamma)
| (* 2 *)
 lt_2 : forall alpha1 alpha2 beta1 beta2 n1 n2 gamma1 gamma2, 
                lt alpha1 alpha2 ->
                lt beta1 (cons alpha2 beta2 0 zero) ->
               lt (cons alpha1 beta1 n1 gamma1)
                  (cons alpha2 beta2 n2 gamma2)
| (* 3 *)
 lt_3 : forall alpha1  beta1 beta2 n1 n2 gamma1 gamma2, 
               lt beta1 beta2 ->
               lt (cons alpha1 beta1 n1 gamma1)
                  (cons alpha1 beta2 n2 gamma2)

| (* 4 *)
 lt_4 : forall alpha1 alpha2 beta1 beta2 n1 n2 gamma1 gamma2, 
               lt alpha2 alpha1 ->
               lt (cons alpha1 beta1 0 zero)  beta2 ->
               lt (cons alpha1 beta1 n1 gamma1)
                  (cons alpha2 beta2 n2 gamma2)

| (* 5 *)
lt_5 : forall alpha1 alpha2 beta1 n1 n2 gamma1 gamma2, 
               lt alpha2 alpha1 ->
               lt (cons alpha1 beta1 n1 gamma1)
                  (cons alpha2  (cons alpha1 beta1 0 zero) n2 gamma2)

| (* 6 *)
lt_6 : forall alpha1 beta1  n1  n2 gamma1 gamma2,  (n1 < n2)%nat ->
                                    lt (cons alpha1 beta1 n1 gamma1)
                                       (cons alpha1 beta1 n2 gamma2)

| (* 7 *)
  lt_7 : forall alpha1 beta1 n1   gamma1 gamma2,  lt gamma1 gamma2 ->
                                      lt (cons alpha1 beta1 n1 gamma1)
                                         (cons alpha1 beta1 n1 gamma2)
where  "o1 < o2" := (lt o1 o2): g0_scope.
Hint Constructors lt.



Open Scope g0_scope.
Definition le t t' := t = t' \/ t < t'.
Hint Unfold le.

Notation "o1 <= o2" := (le o1 o2): g0_scope.
                            
(* Veblen Normal Form *)

Inductive nf : T2 -> Prop :=
| zero_nf : nf zero
| single_nf : forall a b n, nf a ->  nf b -> nf (cons a b n zero)
| cons_nf : forall a b n a' b' n' c', 
                             psi a' b' < psi a b  -> 
                             nf a -> nf b -> 
                             nf(cons a' b' n' c')-> 
                             nf(cons a b n (cons a' b' n' c')).
Hint Resolve zero_nf single_nf cons_nf .

(* inversion lemmas *)

Lemma nf_inv1 : forall a b n c, nf (cons a b n c) -> nf a.
Proof.
  inversion_clear 1; auto.
Qed.

Lemma nf_inv2 : forall a b n c, nf (cons a b n c) -> nf b.
Proof.
 inversion_clear 1; trivial.
Qed.

Fixpoint size (o:T2):nat :=
 match o with zero => 0
            | cons a b n c => S (size a + size b + size c + n )%nat
         end.

Lemma size2 : forall a b n c , (size a < size (cons a b n c))%nat.
Proof.
 simpl; auto with arith.
Qed.

Lemma size3 : forall a b n c , (size b < size (cons a b n c))%nat.
Proof.
 simpl; auto with arith.
Qed.

Lemma size4 : forall a b n c , (size c < size (cons a b n c))%nat.
Proof.
 simpl; auto with arith.
Qed.

Theorem lt_a_cons : forall a b n c,  a < cons a b n c.
Admitted.

Theorem lt_b_cons : forall a b n c, lt b (cons a b n c).
Admitted.

Lemma lt_tail: forall a b n c, nf (cons a b n c) ->  c < cons a b n c. 
Admitted.

Theorem transitivity : forall t1 t2 t3, t1 < t2 -> t2 < t3 -> t1 < t3.
Admitted.

Inductive subterm : T2 -> T2 -> Prop :=
 | subterm_a : forall a b n c, subterm a (cons  a b n c)
 | subterm_b : forall a b n c, subterm b (cons a b n c)
 | subterm_c : forall a b n c, subterm c (cons a b n c)
 | subterm_trans : forall t t1 t2, subterm t t1 -> subterm t1 t2 ->
                                                   subterm t t2.

Lemma nf_subterm : forall alpha beta, subterm alpha beta ->
                                       nf beta -> 
                                       nf alpha.
Proof.
 induction 1.
 inversion 1;auto.
 inversion 1;auto.
 inversion 1;auto.
auto.
Qed.

Lemma psi_relevance : forall alpha beta n gamma  alpha' beta' n' gamma',
        psi alpha beta <  psi alpha' beta' ->
        cons alpha beta n gamma <  cons alpha' beta' n' gamma'.
Admitted.

Definition lt_ge_dec : forall t t', {t<t'}+{t'<=t}.
Admitted.

Lemma lt_irr : forall alpha, ~ alpha < alpha.
Admitted.

Theorem rpo_nat_ord :
  forall n o1 o2 p o3, rpo (nat_translation n) (translation (cons o1 o2 p o3)).
Proof.
intro m; induction m as [ | m].
simpl; intros o1 o2 [ | p] [ | a b n c]; apply Top_gt; simpl; trivial; contradiction.
simpl; intros o1 o2 [ | p] [ | a b n c]; apply Top_gt; simpl; trivial.
intros s [s_eq_transl_m | s_in_nil]; [idtac | contradiction].
subst s; apply (IHm o1 o2 0 zero).
intros s [s_eq_transl_m | s_in_nil]; [idtac | contradiction].
subst s; apply (IHm o1 o2 0 (cons a b n c)).
intros s [s_eq_transl_m | s_in_nil]; [idtac | contradiction].
subst s; apply (IHm o1 o2 (S p) zero).
intros s [s_eq_transl_m | s_in_nil]; [idtac | contradiction].
subst s; apply (IHm o1 o2 (S p) (cons a b n c)).
Qed.

Lemma nf_psi : 
   forall alpha beta n gamma, nf (cons alpha beta n gamma) ->
   gamma < psi alpha beta.
Proof.
intros alpha beta n [ | a b p c].
intros _; unfold psi; apply lt_1.
inversion 1; unfold psi; apply psi_relevance; trivial.
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

Lemma lt_inc_rpo : forall n, 
                           forall o' o, (size o + size o' <= n)%nat->
                              o < o' -> nf o -> nf o' -> 
                                  rpo (translation o) (translation o').
Proof.
intro m; induction m as [ | m].
destruct o' as [ | o1' o2' n' o3'].
inversion 2.
destruct o as [ | o1 o2 n o3]; inversion 1.
destruct o' as [ | o1' o2' n' o3'].
destruct o as [ | o1 o2 n o3]; inversion 2.
destruct o as [ | o1 o2 n o3].
intros _ _ _ _; simpl; destruct n' as [ | n'].
destruct o3'; apply Top_gt; simpl; trivial; contradiction.
apply Top_gt; [simpl; trivial | intros; contradiction].
intros Size o_lt_o' nf_o nf_o'; simpl.
assert (psi_o1_o2_le_psi_o1'_o2' : psi o1 o2 <= psi o1' o2').
destruct (lt_ge_dec (psi o1' o2') (psi o1 o2)) as [ H | H]; trivial.
generalize (transitivity _ _ _ o_lt_o' (psi_relevance o1' o2' n' o3' o1 o2 n o3 H)).
intro; absurd (cons o1 o2 n o3 < cons o1 o2 n o3); trivial; apply lt_irr.
assert (H : psi o1 o2 < psi o1' o2' -> rpo (translation (psi o1 o2)) (translation (psi o1' o2'))).
inversion 1; subst. (* 6 cases *)
(* Case 1 : H2 : o1 < o1'
                   H9 : o2 < cons o1' o2' 0 zero *)
assert (o1_rpo_o1' : rpo (translation o1) (translation o1')).
apply IHm; trivial.
apply  lt_n_Sm_le; refine (Lt.lt_le_trans _ _ _ _ Size); trivial;
apply plus_lt_compat; apply size2.
apply nf_inv1 with o2 n o3; trivial.
apply nf_inv1 with o2' n' o3'; trivial.
unfold psi; simpl; apply Top_eq_lex; simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_o1 | [s_eq_o2 | s_in_nil]].
subst; apply Subterm with (translation o1'); [left | apply Lt]; trivial.
subst; apply (IHm (psi o1' o2') o2); trivial.
apply  lt_n_Sm_le; refine (Lt.lt_le_trans _ _ _ _ Size); trivial;
apply plus_lt_le_compat; [apply size3 | simpl; do 2 rewrite plus_0_r; auto with arith].
apply nf_inv2 with o1 n o3; trivial.
unfold psi; apply single_nf.
apply nf_inv1 with o2' n' o3'; trivial.
apply nf_inv2 with o1' n' o3'; trivial.
contradiction.
(* Case 2 :       o1 = o1' 
                   H : psi o1' o2 < psi o1' o2' *)
assert (o2_rpo_o2' : rpo (translation o2) (translation o2')).
apply IHm; trivial.
apply  lt_n_Sm_le; refine (Lt.lt_le_trans _ _ _ _ Size); trivial;
apply plus_lt_compat; apply size3.
apply nf_inv2 with o1' n o3; trivial.
apply nf_inv2 with o1' n' o3'; trivial.
unfold psi; simpl; apply Top_eq_lex; simpl; trivial.
apply List_eq; apply List_gt; trivial.
intros s [s_eq_o1' | [s_eq_o2 | s_in_nil]].
subst; apply Subterm with (translation o1'); [left | apply Eq]; trivial.
subst; apply Subterm with (translation o2'); [right; left | apply Lt]; trivial.
contradiction.
(* Case 3 : H : psi o1 o2 < psi o1' o2'
                   H2 : o1' < o1
                   H9 : cons o1 o2 0 zero < o2' *)
apply rpo_trans with (translation o2').
simpl; apply Subterm with (translation o2'); [right; left | apply Eq]; trivial.
simpl; apply (IHm o2' (psi o1 o2)); trivial.
apply  lt_n_Sm_le; refine (Lt.lt_le_trans _ _ _ _ Size); trivial;
apply plus_le_lt_compat; [simpl; do 2 rewrite plus_0_r; auto with arith | apply size3].
unfold psi; apply single_nf.
apply nf_inv1 with o2 n o3; trivial.
apply nf_inv2 with o1 n o3; trivial.
apply nf_inv2 with o1' n' o3'; trivial.
(* Case 4 : H : psi o1 o2 < psi o1' (cons o1 o2 0 zero) *)
unfold psi; simpl; 
apply Subterm with (translation (psi o1 o2)); [right; left; trivial | apply Eq].
(* Case 5 : H : psi o1' o2' < psi o1' o2' *)
absurd (psi o1' o2' < psi o1' o2'); trivial; apply lt_irr.
(* Case 6 : H : psi o1' o2' < psi o1' o2' *)
absurd (psi o1' o2' < psi o1' o2'); trivial; apply lt_irr.

assert (o1_rpo_cons_o' : rpo (translation o1) (translation (cons o1' o2' n' o3'))).
apply IHm; trivial.
apply  lt_n_Sm_le; refine (Lt.lt_le_trans _ _ _ _ Size); 
apply plus_lt_le_compat; [apply size2 | apply le_n].
apply transitivity with (cons o1 o2 n o3); trivial; apply lt_a_cons.
apply nf_inv1 with o2 n o3; trivial.

assert (o2_rpo_cons_o' : rpo (translation o2) (translation (cons o1' o2' n' o3'))).
apply IHm; trivial.
apply  lt_n_Sm_le; refine (Lt.lt_le_trans _ _ _ _ Size); 
apply plus_lt_le_compat; [apply size3 | apply le_n].
apply transitivity with (cons o1 o2 n o3); trivial; apply lt_b_cons.
apply nf_inv2 with o1 n o3; trivial.

assert (o3_rpo_cons_o' : rpo (translation o3) (translation (cons o1' o2' n' o3'))).
apply IHm; trivial.
apply  lt_n_Sm_le; refine (Lt.lt_le_trans _ _ _ _ Size); 
apply plus_lt_le_compat; [apply size4 | apply le_n].
apply transitivity with (cons o1 o2 n o3); trivial; apply lt_tail; trivial.
inversion nf_o; trivial.

inversion o_lt_o'; subst. (* 6 cases *)
(* Case 1: H2 : o1 < o1'
H9 : o2 < cons o1' o2' 0 zero
o1_lt_o1' : rpo (translation o1) (translation o1')
H' : psi o1 o2 < psi o1' o2'
H'' : rpo (translation (psi o1 o2)) (translation (psi o1' o2')) *)
assert (o1_lt_o1' : rpo (translation o1) (translation o1')).
apply IHm; trivial.
apply  lt_n_Sm_le; refine (Lt.lt_le_trans _ _ _ _ Size); 
apply plus_lt_compat; apply size2.
apply nf_inv1 with o2 n o3; trivial.
apply nf_inv1 with o2' n' o3'; trivial.

inversion psi_o1_o2_le_psi_o1'_o2' as [H' | H'].
injection H'; intros; subst o1'; absurd (o1 < o1); trivial; apply lt_irr.
assert (H'' := H H').
destruct n as [ | n]; destruct n' as [ | n'].
destruct o3; destruct o3'; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil)); [left | apply Lt]; trivial.
apply Top_gt.
simpl; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
subst; apply (rpo_nat_ord 0 o1' o2' 0 zero).
contradiction.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
subst; apply (rpo_nat_ord 0 o1' o2' 0 (cons o3'1 o3'2 n0 o3'3)).
contradiction.
destruct o3.
subst; apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord 0 o1' o2' (S n') o3').
contradiction.
destruct o3'.
apply Top_gt.
simpl; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
subst; apply (rpo_nat_ord (S n) o1' o2' 0 zero).
contradiction.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord (S n) o1' o2' 0 (cons o3'1 o3'2 n0 o3'3)).
contradiction.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord (S n) o1' o2' (S n') o3').
contradiction.

(* Case 2 : o1 = o1' 
                   H1 : o2 < o2' *)
assert (o2_rpo_o2' : rpo (translation o2) (translation o2')).
apply (IHm o2' o2); trivial.
apply  lt_n_Sm_le; refine (Lt.lt_le_trans _ _ _ _ Size);
apply plus_lt_compat; apply size3; trivial.
apply nf_inv2 with o1' n o3; trivial.
apply nf_inv2 with o1' n' o3'; trivial.

inversion psi_o1_o2_le_psi_o1'_o2' as [H' | H'].
injection H'; intros; subst o2'; absurd (o2 < o2); trivial; apply lt_irr.
assert (H'' := H H').
destruct n as [ | n]; destruct n' as [ | n'].
destruct o3; destruct o3'; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil)); [left | apply Lt]; trivial.
apply Top_gt.
simpl; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
subst; apply (rpo_nat_ord 0 o1' o2' 0 zero).
contradiction.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
subst; apply (rpo_nat_ord 0 o1' o2' 0 (cons o3'1 o3'2 n0 o3'3)).
contradiction.
destruct o3.
subst; apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord 0 o1' o2' (S n') o3').
contradiction.
destruct o3'.
apply Top_gt.
simpl; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
subst; apply (rpo_nat_ord (S n) o1' o2' 0 zero).
contradiction.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord (S n) o1' o2' 0 (cons o3'1 o3'2 n0 o3'3)).
contradiction.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord (S n) o1' o2' (S n') o3').
contradiction.

(* Case 3 : H2 : o1' < o1
                   H9 : cons o1 o2 0 zero < o2' *)
inversion psi_o1_o2_le_psi_o1'_o2' as [H' | H'].
injection H'; intros; subst o2'; absurd (o2 < o2).
apply lt_irr.
apply transitivity with (cons o1 o2 0 zero); trivial; apply lt_b_cons.
assert (H'' := H H').
destruct n as [ | n]; destruct n' as [ | n'].
destruct o3; destruct o3'.
trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply Top_gt.
simpl; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
subst; apply (rpo_nat_ord 0 o1' o2' 0 zero).
contradiction.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord 0 o1' o2' 0 (cons o3'1 o3'2 n0 o3'3)).
contradiction.
destruct o3.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord 0 o1' o2' (S n') o3').
contradiction.
destruct o3'.
apply Top_gt.
simpl; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply (rpo_nat_ord (S n) o1' o2' 0 zero).
contradiction.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord (S n) o1' o2' 0 (cons o3'1 o3'2 n0 o3'3)).
contradiction.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord (S n) o1' o2' (S n') o3').
contradiction.

(* Case 4 : H1 : o1' < o1
                   o_lt_o' : cons o1 o2 n o3 < cons o1' (cons o1 o2 0 zero) n' o3' *)
inversion psi_o1_o2_le_psi_o1'_o2' as [H' | H'].
injection H'; intros; absurd (o2 < o2).
apply lt_irr.
pattern o2 at 2; rewrite H0; apply lt_b_cons.
assert (H'' := H H').
destruct n as [ | n]; destruct n' as [ | n'].
destruct o3; destruct o3'.
trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation (psi o1 o2) :: nil));
[ left | apply Lt ]; trivial.
apply Top_gt.
simpl; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
subst; apply (rpo_nat_ord 0 o1' (psi o1 o2) 0 zero).
contradiction.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation (psi o1 o2) :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord 0 o1' (psi o1 o2) 0 (cons o3'1 o3'2 n0 o3'3)).
contradiction.
destruct o3.
apply Subterm with (Term ord_psi (translation o1' :: translation (psi o1 o2) :: nil));
[ left | apply Lt ]; trivial.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation (psi o1 o2) :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord 0 o1' (psi o1 o2) (S n') o3').
contradiction.
destruct o3'.
apply Top_gt.
simpl; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply (rpo_nat_ord (S n) o1' (psi o1 o2) 0 zero).
contradiction.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation (psi o1 o2) :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord (S n) o1' (psi o1 o2) 0 (cons o3'1 o3'2 n0 o3'3)).
contradiction.
apply Top_eq_lex.
simpl; trivial.
apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation (psi o1 o2) :: nil));
[ left | apply Lt ]; trivial.
apply (rpo_nat_ord (S n) o1' (psi o1 o2) (S n') o3').
contradiction.

(* Case 5 : H1 : (n < n')%nat
                   o_lt_o' : cons o1' o2' n o3 < cons o1' o2' n' o3' *)
clear H; clear psi_o1_o2_le_psi_o1'_o2'.
assert (n_rpo_n' := lt_nat_inc_rpo n n' H1).
destruct n as [ | n]; destruct n' as [ | n'].
absurd (0<0)%nat; auto with arith.
destruct o3.
subst; apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Eq]; trivial.
apply Top_eq_lex.
simpl; trivial.
apply List_eq; apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Eq ]; trivial.
apply (rpo_nat_ord 0 o1' o2' (S n') o3').
contradiction.
absurd (S n < 0)%nat; auto with arith.
apply Top_eq_lex.
simpl; trivial.
apply List_eq; apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_S_n | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Eq ]; trivial.
apply (rpo_nat_ord (S n) o1' o2' (S n') o3').
contradiction.

(* Case 6 : H1 : o3 < o3'
                   o_lt_o' : cons o1' o2' n' o3 < cons o1' o2' n' o3' *)
clear H; clear psi_o1_o2_le_psi_o1'_o2'.
assert (o3_rpo_o3' : rpo (translation o3) (translation o3')).
apply (IHm o3' o3); trivial.
apply  lt_n_Sm_le; refine (Lt.lt_le_trans _ _ _ _ Size);
apply plus_lt_compat; apply size4; trivial.
inversion nf_o; trivial.
inversion nf_o'; trivial.

destruct n' as [ | n'].
destruct o3; destruct o3'.
absurd (zero < zero); trivial; apply lt_irr.
subst; apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Eq]; trivial.
inversion H1.
apply Top_eq_lex.
simpl; trivial.
do 2 apply List_eq; apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Eq ]; trivial.
apply (rpo_nat_ord 0 o1' o2' 0 (cons o3'1 o3'2 n0 o3'3)).
contradiction.
apply Top_eq_lex.
simpl; trivial.
do 2 apply List_eq; apply List_gt; trivial.
intros s [s_eq_psi_o1_o2 | [s_eq_0 | [s_eq_o3 | s_in_nil]]]; subst; trivial.
apply Subterm with (Term ord_psi (translation o1' :: translation o2' :: nil));
[ left | apply Eq ]; trivial.
apply (rpo_nat_ord (S n') o1' o2' (S n') o3').
contradiction.
Qed.

