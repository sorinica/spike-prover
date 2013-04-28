Require Import Lt.
Require Import Relations.
Require Import Wf_nat.
Require Import List.


Notation "[ a , .. , b ]" := ( cons a .. (cons b nil) .. )
  (at level 0, a at level 99, b at level 99).


(** Some usual computational relations over naturals. *)
Fixpoint beq_nat (x y:nat) : bool :=
match x,y with
| 0,0 => true
| S x', S y' => beq_nat x' y'
| _, _ => false
end.

Lemma beq_nat_true: forall m n, beq_nat m n = true -> m = n.
Proof.
refine (
fix f m n :=
match m,n with
| 0,0 => _
| S x', S y' => _
| _, _ => _
end
); simpl; intro H.
reflexivity.
discriminate H.
discriminate H.
apply eq_S, f, H.
Defined.

Lemma beq_nat_false: forall m n, beq_nat m n = false -> m <> n.
Proof.
refine (
fix f m n :=
match m,n with
| 0,0 => _
| S x', S y' => _
| _, _ => _
end
); simpl; intro H.
discriminate H.
intros H1; discriminate H1.
intros H1; discriminate H1.
cut (x' <> y').
apply not_eq_S.
apply f, H.
Defined.

Theorem beq_nat_ok: forall m n, if beq_nat m n then m = n else m <> n.
Proof.
intros m n; case_eq (beq_nat m n).
apply beq_nat_true.
apply beq_nat_false.
Defined.

Theorem beq_eq: forall x y, beq_nat x y = true <-> x=y.
Proof.
intros x y; split.
apply beq_nat_true.
intro H; rewrite H; clear H x.
induction y.
reflexivity.
simpl; assumption.
Qed.

Fixpoint blt_nat (x y:nat) : bool :=
match x,y with
| _,0 => false
| 0,S _ => true
| S x', S y' => blt_nat x' y'
end.

Theorem blt_lt: forall x y, blt_nat x y = true <-> x < y.
Proof.
refine (fix IH x y :=
match x,y with
| _,0 => _
| 0,S _ => _
| S x', S y' => _
end); simpl; split; intro H; trivial; try (discriminate H || inversion H).
apply Lt.lt_O_Sn.
apply Lt.lt_n_S; apply -> IH; trivial.
apply <- IH; constructor.
apply <- IH; apply Lt.lt_S_n; trivial.
Qed.


Theorem blt_nat_irrefl : forall x, ~ blt_nat x x = true.
Proof.
intros x H; apply Lt.lt_irrefl with x; apply -> blt_lt; trivial.
Qed.

Theorem blt_nat_trans : forall x y z,
  blt_nat x y = true -> blt_nat y z = true -> blt_nat x z = true.
Proof.
intros x y z Hxy Hyz; apply <- blt_lt; apply Lt.lt_trans with y; apply -> blt_lt; trivial.
Qed.



(** Noehterian induction over subset of elements of a well-founded relation. *)
Section wf_subset.

  Variable T : Type.
  Variable R : T -> T -> Prop.
  Hypothesis wf_R: well_founded R.
  Variable S : T -> Prop. (* subset of elements of T *)
  Variable P : T -> Prop. (* properties on the elements of T *)

  Hypothesis S_acc : forall x, S x -> (forall y, S y -> R y x -> P y) -> P x.

  Theorem wf_subset : forall x, S x -> P x.
  Proof.
  intro z; elim (wf_R z).
  intros x H1x H2x H3x.
  apply S_acc; trivial.
  intros y H1y H2y; apply H2x; trivial.
  Qed.

End wf_subset.



(** Necessary lemmas for building a Symb module. *)
Section init_symb.

  Variable A: Type.
  Hypothesis symb_eq_dec: forall x y:A, {x=y}+{x<>y}.

  Definition eq_bool (x y:A) : bool :=
      if symb_eq_dec x y then true else false.

  Theorem eq_bool_ok : forall x y,
      if eq_bool x y then x = y
      else ~ x = y.
  Proof.
  unfold eq_bool.
  intros x y; case (symb_eq_dec x y); trivial.
  Defined.

End init_symb.


(** Necessary lemmas for building a Prec module. *)
Section init_prec.

  Variable A: Type.
  Variable index: A -> nat.

  Definition prec_bool (x y:A) : bool :=
    blt_nat (index x) (index y).
  Definition prec (x y:A) := prec_bool x y = true.

  Theorem prec_bool_ok x y : if prec_bool x y then prec x y else ~prec x y.
  Proof.
  intros x y; case_eq (prec_bool x y); trivial.
  intros H H'; rewrite H' in H; discriminate H.
  Defined.

  Theorem prec_antisym : forall x, ~ prec x x.
  Proof.
  intro x; apply blt_nat_irrefl.
  Qed.

  Theorem prec_transitive : transitive A prec.
  Proof.
  intros x y z; apply blt_nat_trans.
  Qed.


  Definition prec_eq (x y:A) : Prop := index x = index y.
  Definition prec_eq_bool (x y:A) : bool := beq_nat (index x) (index y).

  Lemma prec_eq_bool_ok: forall a1 a2, match prec_eq_bool a1 a2 with true => prec_eq a1 a2 | false => ~prec_eq a1 a2 end.
  Proof.
  intros a1 a2; apply beq_nat_ok.
  Qed.

  Lemma prec_eq_transitive: transitive A prec_eq.
  Proof.
  intros x y z; unfold prec_eq; apply trans_eq.
  Qed.

  Lemma prec_eq_sym : forall s t, prec_eq s t -> prec_eq t s.
  Proof.
  intros x y; unfold prec_eq; apply sym_eq.
  Qed.

  Lemma prec_eq_refl : forall s, prec_eq s s.
  Proof.
  intros x; unfold prec_eq; apply refl_equal.
  Qed.

  Lemma prec_eq_prec1: forall a1 a2 a3, prec a1 a2 -> prec_eq a2 a3 -> prec a1 a3.
  Proof.
  intros x y z Hxy Hyz.
  unfold prec, prec_bool; elim Hyz.
  apply Hxy.
  Qed.

  Lemma prec_eq_prec2: forall a1 a2 a3, prec a1 a2 -> prec_eq a1 a3 -> prec a3 a2.
  Proof.
  intros x y z Hxy Hyz.
  unfold prec, prec_bool; elim Hyz.
  apply Hxy.
  Qed.
  
  Lemma prec_not_prec_eq: forall f g, prec f g -> prec_eq f g -> False.
  Proof.
  intros x y H1 H2.
  apply blt_nat_irrefl with (index x).
  pattern (index x) at 2; rewrite H2; apply H1.
  Qed.

  Theorem prec_wf: well_founded prec.
  Proof.
  apply Wf_nat.well_founded_lt_compat with (f:=index).
  intros x y; apply -> blt_lt.
  Qed.

End init_prec.



(** Some tactics *)
Lemma nth_In: forall T n l, forall x:T, nth_error l n = value x -> In x l.
Proof.
intros T n; induction n; induction l; intros x H; try discriminate H.
injection H; clear H; intro H; rewrite H; left; trivial.
right; apply IHn, H.
Qed.

(* Quickly solve a goal of the form 'In x l' when its position in [l] is given *)
Ltac trivial_in m :=
match goal with
| |- In ?X ?Y =>
  apply nth_In with (n:=m);
  lazy delta [nth_error] beta iota delta [Y];
  reflexivity
end.

(* Unfold all cases for all hypotheses of the form [In x l] *)
Ltac case_In_rec H :=
match type of H with
| In ?X ?Y =>
  elim H; clear H; intro H; case_In_rec H
| _ => idtac
end.

Ltac case_In H :=
match type of H with
| In ?X ?Y =>
    case_In_rec H;
    elim H; try (clear H); try (clear X)
| _ => fail "hypothesis has not type [In _ _]"
end.

(* From Program.Tactics *)
Ltac do_nat n tac :=
match n with
| 0 => idtac
| S ?n' => tac ; do_nat n' tac
end.


(** Tool lemmas for parallelization. *)
Section flatten_list.

  Variable A: Type.
  Variable P: A -> Prop.

  Fixpoint flatten (ll: list (list A)) : list A :=
  match ll with
  | nil => nil
  | l::ll' => l ++ (flatten ll')
  end.

  Lemma combine : forall ll:list (list A), 
    (forall l, In l ll -> forall x, In x l -> P x) ->
      forall x, In x (flatten ll) -> P x.
  Proof.
  intros ll; elim ll.
  intros _ x Hx; elim Hx.
  intros l ll' H1 H2.
  intros x Hx.
  elim (in_app_or _ _ x Hx).
  apply H2; left; reflexivity.
  apply H1.
  intros l' Hl'; apply H2; right; assumption.
  Qed.

End flatten_list.
Implicit Arguments flatten [A].
Implicit Arguments combine [A].