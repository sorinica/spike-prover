Require Import List.
Require Import Relations.

Require Import Coccinelle.term.
Require Import Coccinelle.rpo.
Require Import list_permut.
Require Import Setoid.

Module Make
  (T1: term_spec.Term).
  (* (P1: Precedence with Definition A := T1.symbol). *)
  Module R := rpo.Make T1.
  Export T1.
  Export R.

  (** Multiset extension of rpo is well-founded *)
  Lemma wf_rpo_mul : forall pr, well_founded (prec pr) -> forall bb, well_founded (rpo_mul pr bb).
  Proof.
  intros pr wf_prec bb0.
  unfold well_founded.
  apply (well_founded_induction_type (wf_rpo_mul_rest pr bb0)).
  intros l Hl; constructor; intros l' Hl'.
  apply Hl.
  constructor; trivial; intros s Hs; apply (wf_rpo pr wf_prec bb0 s).
  Qed.


  (** Order on couples using rpo_mul on the second projection. *)
  Definition snd_rpo_mul prec {B:Type} n (f1 f2: B * (list term)) := rpo_mul prec n (snd f1) (snd f2).

  Lemma wf_snd_rpo_mul : forall pr, well_founded (prec pr) -> forall bb B, well_founded (@snd_rpo_mul pr B bb).
  Proof.
  intros pr wf_prec n B (z,pz); revert z.
  elim (wf_rpo_mul pr wf_prec n pz); intros x _ H.
  intro z; constructor; intros (y,py) Hy.
  apply H; exact Hy.
  Qed.


  (** rpo_mul version of an existing lemma about rpo. *)
  Function is_a_pos_list (l : list term) (p : list nat) {struct p}: bool :=
  match p with
  | nil => true
  | i :: q =>
    match nth_error l i with
    | Some ti => is_a_pos ti q
    | None => false
    end
  end.

  Lemma rpo_mul_add_context :
    forall pr bb i p l s t, rpo pr bb s t -> is_a_pos_list l (i::p) = true -> 
    rpo_mul pr bb (replace_at_pos_list l s i p) (replace_at_pos_list l t i p).
  Proof.
  intros pr bb0 i p l s t H0 H.
  generalize i H; clear i H; induction l as [ | u l]; intros i H; simpl.
  simpl in H; destruct i; discriminate.
  destruct i as [ | i].
  apply (@List_mul pr bb0 (replace_at_pos u t p) nil (replace_at_pos u s p :: nil) l). assert (H1: ((replace_at_pos u s p :: l) = ((replace_at_pos u s p :: nil) ++ l))). 
reflexivity. rewrite H1. apply permut_refl. intros. apply Eq. assert (H1: ((replace_at_pos u t p :: l) = (replace_at_pos u t p :: nil ++ l))). 
reflexivity. rewrite H1. apply permut_refl. intros. apply Eq.


  intros b [b_eq_s' | b_mem_nil].
  exists (replace_at_pos u t p); split.  unfold more_list.mem. left. apply equiv_refl. apply equiv_equiv.


  rewrite (equiv_rpo_equiv_2 _ b_eq_s').
  apply rpo_add_context; trivial.
  contradiction.
  simpl in IHl; simpl in H; assert (H' := IHl i H).
  inversion H' as [a lg ls lc l' l'' ls_lt_alg P1 P2]; subst.
  apply (@List_mul pr bb0 a lg ls (u :: lc)); trivial.
  rewrite <- permut0_cons_inside; trivial; try reflexivity. apply equiv_equiv. apply equiv_refl. apply equiv_equiv. 
  rewrite app_comm_cons.
  rewrite <- permut0_cons_inside; trivial; try reflexivity. apply equiv_equiv.  apply equiv_refl. apply equiv_equiv.
  Qed.


  (** Some tactics to solve goals of the form [rpo_mul l1 l2]. *)

  (* Tell if the term [var] is in the list [lvar] *)
  Ltac mem_assoc var lvar :=
  match constr:(lvar) with
  | nil => constr:(false)
  | ?X1 :: ?X2 =>
      match constr:(X1 = var) with
      | (?X1 = ?X1) => constr:(true)
      | _ => mem_assoc var X2
      end
  end.

  (* Build a substitution from the list of elements [lvar] *)
  Ltac build_subst lvar :=
  let rec build_aux lvar cpt :=
    match constr:(lvar) with
    | (@nil ?X1) => constr:(@nil (prod nat X1))
    | ?X2 :: ?X3 =>
        let l2 := build_aux X3 (S cpt) in
        constr:((cpt,X2) :: l2)
    end
  in build_aux lvar 0.

  (* Create the substitution associated to the term [trm] *)
  Ltac seek_var lvar trm :=
    match constr:(trm) with
    | Var ?X1 => constr:(lvar)
    | Term ?X1 ?X2 => seek_var_list lvar X2
    | ?X1 =>
        let res := mem_assoc X1 lvar in
        match constr:(res) with
        | true => constr:(lvar)
        | false => constr:(X1 :: lvar)
        end
    end

  with seek_var_list lvar lst :=
    match constr:(lst) with
    | nil => lvar
    | cons ?X1 ?X2 =>
      let l1 := seek_var lvar X1 in
        seek_var_list l1 X2
    end.

  (* Return the integer associated to [elt] in [lst] *)
  Ltac assoc elt lst :=
  match constr:(lst) with
  | nil => fail
  | (?X1,?X2) :: ?X3 =>
      match constr:(elt = X2) with
      | (?X2 = ?X2) => constr:(X1)
      | _ => assoc elt X3
      end
  end.

  (* Given a substitution [lvar], returns the term [trm] where
  everything different from [Var _] or [Term _ _] is replaced
  by [Var n]. *)
  Ltac interp lvar trm :=
    match constr:(trm) with
    | Var _ => constr:(trm)
    | Term ?X1 ?X2 => let l := interp_list lvar X2 in
      constr:(Term X1 l)
    | ?X1 => let idx := assoc X1 lvar in
           constr:(Var idx)
    end

  with interp_list lvar lst :=
  match constr:(lst) with
  | nil => constr:(lst)
  | ?X1::?X2 =>
    let x := interp lvar X1 in
    let l := interp_list lvar X2 in
    constr:(x::l)
  end.

  (* Solve a goal of the form 'rpo_mul _ _' *)
  Ltac solve_rpo_mul :=
  intros;
  match goal with
  | |- rpo_mul ?p ?n ?X1 ?X2 =>
    let lvar1 := seek_var_list (@nil term) X1 in
    let lvar := seek_var_list lvar1 X2 in
    let sigma := build_subst lvar in
    let lt1 := interp_list sigma X1 in
    let lt2 := interp_list sigma X2 in
    change (rpo_mul p n
      (map (apply_subst sigma) lt1)
      (map (apply_subst sigma) lt2)
    )
  end;
  apply rpo_mul_subst;
  apply rpo_mult_eval_rpo_mul_less;
  vm_compute; reflexivity.

End Make.
