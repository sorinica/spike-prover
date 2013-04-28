(*
let F = signature "m : 3; i : 1;";
let X = variables "x, y, x', y'";
let T = algebra F;


unify (term T "m(x,y,i(y))") (term T "m(y',x',x')");


*)

Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/basis".
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/list_extensions". 
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/term_algebra". 
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/term_orderings". 
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/unification".
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/examples/cime_trace".

Require terminaison.

Require Relations.

Require term.

Require List.

Require equational_theory.
Require Import ordered_set.

Require term_extension.
Require Import free_unif.

Require Inclusion.


Require ZArith.

Require Zwf.

Require Inverse_Image.

Import List.

Import ZArith.

Set Implicit Arguments.


Module algebra.
 Module F<:term.Signature.
  Inductive symb  :
   Set := 
    | m : symb
    | i : symb
  .
  
  
   (* Proof of decidability of equality over symb *)
  Definition symb_eq_dec(f1 f2:symb) : {f1 = f2}+{f1 <> f2}.
  Proof.
    intros f1 f2.
    case f1; case f2.
    left; reflexivity.
    right; discriminate.
    right; discriminate.
    left; reflexivity.
  Defined. 

  Definition arity (f:symb) := 
    match f with
      | m => term.Free 3
      | i => term.Free 1
      end.
  
  
  Module Symb.
   Definition A  := symb.
   
   Definition eq_dec  := symb_eq_dec.
  End Symb.
  
  Export Symb.
 End F.
 
 Module Alg := term.Make'(F)(term_extension.IntVars).
End algebra.

Import algebra.
Import F.
Import Relation_Definitions.


Module OF. 

Definition A := symb.
Definition eq_dec := eq_dec. 
Definition o (f1 f2:symb) : Prop :=
match f1,f2 with 
  | m,m => True
  | i,i => True
  | i,m => True 
  | _,_ => False
end.

Definition o_proof : order A o.
Proof.
  constructor.
  intros f;case f;exact I.

  intros f g;case f;case g;clear f g;simpl;intro h;try tauto;intros _;
    case h;tauto.

  intros f g;case f;case g;clear f g;simpl;tauto.

Defined.

Definition o_dec : forall e1 e2 : A, {o e1 e2} + {~ o e1 e2}.
Proof.
  intros f g;case f;case g; clear f g;simpl;(complete (left;tauto))||(right;tauto).
Defined.


Lemma o_total : forall e1 e2 : A, {o e1 e2} + {o e2 e1}.
Proof.
  intros f g;case f;case g; clear f g;simpl;(complete (left;tauto))||(right;tauto).
Qed.
End OF.


Module Unif := free_unif.Make(Alg)(OF)(ordered_set.Nat).
Import Alg.

Definition t1 :=
  Term m (Var 0::Var 1::(Term i (Var 1::nil))::nil).

Definition t2 :=
  Term m (Var 2::Var 3::Var 3::nil).

Import Unif.

Definition pb := mk_pb nil ((t1,t2)::nil).
Definition ex_pb := Normal _ pb.

Definition exc_pb_ok  := OK ex_pb (inv_solved_part_init t1 t2).
Definition dec_pb := decompose exc_pb_ok.

Definition pb1 := (decomposition_step pb). 
Eval vm_compute in pb1.
Definition pb2 := (decomposition_step ((mk_pb nil
            ((Var 0, Var 2)
             :: (Var 1, Var 3) :: (Term i (Var 1 :: nil), Var 3) :: nil)))). 
Eval vm_compute in pb2.
Definition pb3 := (decomposition_step (mk_pb ((0, Var 2) :: nil)
            ((Var 1, Var 3) :: (Term i (Var 1 :: nil), Var 3) :: nil))).
Eval vm_compute in pb3.
Definition pb4 := (decomposition_step (mk_pb ((1, Var 3) :: (0, Var 2) :: nil)
            ((Term i (Var 3 :: nil), Var 3) :: nil))).
Eval vm_compute in pb4.
Definition pb5 := (decomposition_step (mk_pb
            ((3, Term i (Var 3 :: nil)) :: (1, Var 3) :: (0, Var 2) :: nil)
            nil)).
Eval vm_compute in pb5.

(* Lemma le_lemme_a_prouver :
forall u1 u2, let pb := mk_pb nil ((u1,u2)::nil) in
 {forall tau, is_a_solution pb tau -> False} +
 {mgu : substitution | forall tau, is_a_solution pb tau <->
   (exists theta, 
   (forall x, apply_subst tau (Var x) = apply_subst theta (apply_subst mgu (Var x))))}. 

Lemma le_lemme_a_prouver :
forall u1 u2, let pb := mk_pb nil ((u1,u2)::nil) in
 {mgu : substitution | forall tau, is_a_solution pb tau <->
   (exists theta, 
   (forall x, apply_subst tau (Var x) = apply_subst theta (apply_subst mgu (Var x))))}
+{forall tau, is_a_solution pb tau -> False}.
*)

Definition u1' := (Term i (Var 0::nil)).

Definition u2' := (Term i (Var 1::nil)).

Definition u1 := Var 0.
Definition u2 := Var 0.

Definition pbu := mk_pb nil ((u1,u2)::nil). 
(* Definition pbu := mk_pb nil nil. *)
Definition ex_pbu := Normal _ pbu.

Definition inv_solved_part_empty : Inv_solved_part (mk_pb nil nil).
unfold Inv_solved_part; simpl; trivial.
Defined.

Definition exc_pb_oku  := OK ex_pbu (inv_solved_part_init u1 u2). 

(* Definition exc_pb_oku  := OK ex_pbu inv_solved_part_empty. *)
Definition dec_pbu := decompose exc_pb_oku.

Definition ex_pb_oku1 := decomposition_step pbu.

Lemma toto : 
lt_weight_exc_pb_ok (weight_exc_pb_ok (decomposition_step_e exc_pb_oku)) (weight_exc_pb_ok exc_pb_oku).
Proof.
vm_compute.
auto with arith.
Defined.

Print lt_mul.

Definition lt_dec (n1 n2 : nat) : {n1 < n2} + {~ n1 < n2}.
intro n1; induction n1 as [ | n1]; intros [ | n2].
right; intro H; inversion H.
left; apply le_n_S; apply le_O_n.
right; intro H; inversion H.
case (IHn1 n2); intro H.
left; apply (le_n_S _ _ H). 
right; intro H'; apply H.
apply (le_S_n _ _ H').
Defined.

Definition lt_mul2 m1 m2 := dickson.NatMul.mult lt lt_dec m1 m2 = Less_than.

Definition lt_ms2 := 
(fun p123 q123 : nat * (list dickson.NatMul.DS.A * nat) =>
let (p1, y) := p123 in
let (p2, p3) := y in
let (q1, y0) := q123 in
let (q2, q3) := y0 in
if eq_nat_dec p1 q1
then 
  match dickson.NatMul.mult lt lt_dec p2 q2 with
  | Equivalent => p3 < q3
  | Less_than => True 
  | _ => False
  end
else p1 < q1)
     : nat * (list dickson.NatMul.DS.A * nat) ->
       nat * (list dickson.NatMul.DS.A * nat) -> Prop.

Definition lt_weight_exc_pb_ok2 := 
(fun w1 w2 : nat * (nat * (list nat * nat)) =>
let (n1, m1) := w1 in
let (n2, m2) := w2 in if eq_nat_dec n1 n2 then lt_ms2 m1 m2 else n1 < n2)
     : nat * (nat * (list nat * nat)) ->
       nat * (nat * (list nat * nat)) -> Prop.

Lemma toto2 : Acc lt_weight_exc_pb_ok2 (weight_exc_pb_ok exc_pb_oku).
Proof.
unfold lt_weight_exc_pb_ok.
simpl.
unfold pbu, measure_for_unif_pb, phi1, phi2, phi3.
progress simpl.
progress (unfold VSet.cardinal).
progress (unfold VSet.filter).
progress (unfold VSet.singleton).
progress (unfold VSet.union).
progress (simpl VSet.support).
progress (unfold size_of_unsolved_part).
progress simpl.
progress (unfold nb_var_eq_of_unsolved_part).
progress simpl.
vm_compute.
simpl.
progress (simpl solved_part).
progress (simpl set_of_variables_in_unsolved_part).
progress (simpl set_of_variables_in_range_of_subst).

progress (simpl VSet.without_red_filter_aux).
progress (unfold is_a_not_solved_var_dec).
progress (unfold is_a_solved_var_dec).
progress (simpl length).
progress (unfold size_of_solved_part).
progress (unfold size_of_unsolved_part).
progress (simpl solved_part).
progress (simpl unsolved_part).
progress (simpl list_size_mul).
progress (simpl app).
progress (simpl more_list.list_size).
progress (unfold well_founded_ind).
progress (unfold well_founded_induction_type).
progress (unfold VSet.filter_aux).


vm_compute.
Lemma dummy : dec_pbu = @No_solution _.
progress (unfold dec_pbu).
progress (unfold exc_pb_oku).
progress (unfold ex_pbu).
progress (unfold pbu).
unfold u1, u2.
progress (unfold decompose).
progress (unfold Fix).
progress (unfold wf_lt_exc_pb_ok).
progress (unfold Inverse_Image.wf_inverse_image).
progress (unfold Inverse_Image.Acc_inverse_image).
progress (unfold Inverse_Image.Acc_lemma).
progress (unfold Acc_ind).
progress (unfold  lt_weight_exc_pb_ok).
progress (unfold weight_exc_pb_ok).
progress (unfold measure_for_unif_pb).
progress (unfold phi1, phi2, phi3).
progress (simpl unsolved_part).
progress (simpl solved_part).
progress (simpl set_of_variables_in_unsolved_part).
progress (simpl set_of_variables_in_range_of_subst).
progress (unfold VSet.singleton).
progress (unfold VSet.union).
progress (simpl VSet.support).
progress (unfold VSet.filter).
progress (simpl VSet.without_red_filter_aux).
progress (unfold is_a_not_solved_var_dec).
progress (unfold is_a_solved_var_dec).
progress (unfold VSet.cardinal).
progress (simpl length).
progress (unfold size_of_solved_part).
progress (unfold size_of_unsolved_part).
progress (simpl solved_part).
progress (simpl unsolved_part).
progress (unfold nb_var_eq_of_unsolved_part).
progress (simpl list_size_mul).
progress (simpl app).
progress (simpl more_list.list_size).
progress (unfold well_founded_ind).
progress (unfold well_founded_induction_type).
progress (unfold VSet.filter_aux).

progress (unfold F_decompose).
progress (unfold decomposition_step_e).
progress (unfold decomposition_step).
progress (unfold lt_wf).
progress (unfold well_founded_ltof).
progress (simpl nat_ind).
progress (unfold Acc_rect).
progress (unfold eq_variable_dec).
progress (simpl Acc_intro).
progress (unfold lt_ms).
progress (unfold size_of_unsolved_part).

progress (unfold VSet.union).


progress (simpl VSet.without_red_filter_aux).
progress (simpl more_list.find).
progress (unfold VSet.cardinal).
progress (unfold eq_variable_dec).


progress (simpl VSet.support).
progress (simpl app).
progress (simpl length).
progress (unfold eq_term_dec).
progress (unfold eq_variable_dec).
progress (unfold VSet.mem_dec).
progress (unfold VSet.LP.mem_dec).
progress (unfold DecVar.eq_dec).
progress (unfold more_list.find).
progress (unfold VSet.add_without_red).
progress (unfold VSet.LP.mem_dec).

************************************************

progress (simpl ).
well_founded_induction_type).

progress (simpl nat_ind).


progress (simpl dickson.NatMul.LP.permut_dec).

progress (simpl well_founded_ind).

progress simpl.

progress (simpl VSet.union).

progress simpl.

cbv beta.

progress simpl.
progress (unfold decomposition_step).
compute.
progress (unfold is_a_not_solved_var_dec).

progress (unfold VSet.cardinal).
progress (unfold is_a_solved_var_dec).
progress (unfold nb_var_eq_of_unsolved_part).

progress (simpl domain_of_subst).
unfold VSet.union.
unfold VSet.singleton.
progress (simpl VSet.support).
unfold VSet.add_without_red.
progress (simpl more_list.list_size).
progress (simpl list_size_mul).
progress (simpl app).
progress (simpl length).
unfold well_founded_induction_type.
unfold lt_wf.
unfold well_founded_ltof.
progress (unfold size).
progress (unfold Acc_ind).
progress simpl.
progress (unfold closure.trans_clos_ind).
progress (simpl dickson.NatMul.LP.permut_dec).

progress (simpl VSet.support).
progress (simpl size).
progress (unfold VSet.filter_aux).
unfold set_of_variables_in_range_of_subst.
progress simpl.
unfold list_rec.
unfold VSet.support.
unfold domain_of_subst.
unfold eq_variable_dec.
unfold nat_rec.
unfold set_of_variables_in_unsolved_part.
unfold set_of_variables.
unfold lt_exc_pb_ok.
progress simpl.
progress (unfold is_a_solved_var).
progress simpl.
unfold VSet.singleton.
unfold well_founded_ind.
unfold decomposition_step.
unfold more_list.find.
unfold apply_subst.
unfold map_subst.
unfold eq_symbol_dec.
unfold Inv_solved_part.
unfold symb_eq_dec.
unfold decomposition_step_decreases_e.

progress simpl.
unfold decomposition_e_unfold_normal.
unfold Fix.
progress simpl.
unfold list_size_mul.
progress simpl.
unfold nb_var_eq_of_unsolved_part.
progress simpl.
unfold u1, u2.
unfold decomposition_step.
progress simpl.
unfold dickson.NatMul.LP.mem_dec.
progress simpl.
unfold dickson.NatMul.LP.mem_split_set.
progress simpl.
unfold Fix, Fix_F, Acc_inv.
unfold wf_lt_ms.
unfold size_of_solved_part.


progress simpl.


vm_compute.dickson.NatMul.LP.mem_dec
simpl.



Ltac set_tac := 
  match goal with 
    | |- ?f ?a = _ => 
      let fn := fresh "f" in 
        let an := fresh "a" in 
        set (fn:=f) in *;
          set (an:=a) in *
    | |- ?f ?a1 ?a2 = _ => 
      let fn := fresh "f" in 
        let a1n := fresh "a" in 
        let a2n := fresh "a" in 
        set (fn:=f) in *;
          set (a1n:=a1) in *;
          set (a2n:=a2) in *
    | |- ?f ?a1 ?a2 ?a3 = _ => 
      let fn := fresh "f" in 
        let a1n := fresh "a" in 
        let a2n := fresh "a" in 
        let a3n := fresh "a" in 
        set (fn:=f) in *;
          set (a1n:=a1) in *;
          set (a2n:=a2) in *;
          set (a3n:=a3) in *
    | |- ?f ?a1 ?a2 ?a3 ?a4 = _ => 
      let fn := fresh "f" in 
        let a1n := fresh "a" in 
        let a2n := fresh "a" in 
        let a3n := fresh "a" in 
        let a4n := fresh "a" in 
        set (fn:=f) in *;
          set (a1n:=a1) in *;
          set (a2n:=a2) in *;
          set (a3n:=a3) in *;
          set (a4n:=a4) in *
    | |- ?f ?a1 ?a2 ?a3 ?a4 ?a5 = _ => 
      let fn := fresh "f" in 
        let a1n := fresh "a" in 
        let a2n := fresh "a" in 
        let a3n := fresh "a" in 
        let a4n := fresh "a" in 
        let a5n := fresh "a" in 
        set (fn:=f) in *;
          set (a1n:=a1) in *;
          set (a2n:=a2) in *;
          set (a3n:=a3) in *;
          set (a4n:=a4) in *;
          set (a5n:=a5) in *
    | |- ?f ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 = _ => 
      let fn := fresh "f" in 
        let a1n := fresh "a" in 
        let a2n := fresh "a" in 
        let a3n := fresh "a" in 
        let a4n := fresh "a" in 
        let a5n := fresh "a" in 
        let a6n := fresh "a" in 
        set (fn:=f) in *;
          set (a1n:=a1) in *;
          set (a2n:=a2) in *;
          set (a3n:=a3) in *;
          set (a4n:=a4) in *;
          set (a5n:=a5) in *;
          set (a6n:=a6) in *
  end.


Ltac set_tac_in h := 
  let e := eval unfold h in h in 
  match e with 
    | ?f ?a  => 
      let fn := fresh "f" in 
        let an := fresh "a" in 
        set (fn:=f) in *;
          set (an:=a) in *
    | ?f ?a1 ?a2  => 
      let fn := fresh "f" in 
        let a1n := fresh "a" in 
        let a2n := fresh "a" in 
        set (fn:=f) in *;
          set (a1n:=a1) in *;
          set (a2n:=a2) in *
    | ?f ?a1 ?a2 ?a3 => 
      let fn := fresh "f" in 
        let a1n := fresh "a" in 
        let a2n := fresh "a" in 
        let a3n := fresh "a" in 
        set (fn:=f) in *;
          set (a1n:=a1) in *;
          set (a2n:=a2) in *;
          set (a3n:=a3) in *
    | ?f ?a1 ?a2 ?a3 ?a4  => 
      let fn := fresh "f" in 
        let a1n := fresh "a" in 
        let a2n := fresh "a" in 
        let a3n := fresh "a" in 
        let a4n := fresh "a" in 
        set (fn:=f) in *;
          set (a1n:=a1) in *;
          set (a2n:=a2) in *;
          set (a3n:=a3) in *;
          set (a4n:=a4) in *
    | ?f ?a1 ?a2 ?a3 ?a4 ?a5  => 
      let fn := fresh "f" in 
        let a1n := fresh "a" in 
        let a2n := fresh "a" in 
        let a3n := fresh "a" in 
        let a4n := fresh "a" in 
        let a5n := fresh "a" in 
        set (fn:=f) in *;
          set (a1n:=a1) in *;
          set (a2n:=a2) in *;
          set (a3n:=a3) in *;
          set (a4n:=a4) in *;
          set (a5n:=a5) in *
    | ?f ?a1 ?a2 ?a3 ?a4 ?a5 ?a6  => 
      let fn := fresh "f" in 
        let a1n := fresh "a" in 
        let a2n := fresh "a" in 
        let a3n := fresh "a" in 
        let a4n := fresh "a" in 
        let a5n := fresh "a" in 
        let a6n := fresh "a" in 
        set (fn:=f) in *;
          set (a1n:=a1) in *;
          set (a2n:=a2) in *;
          set (a3n:=a3) in *;
          set (a4n:=a4) in *;
          set (a5n:=a5) in *;
          set (a6n:=a6) in *
  end.

Goal dec_pb= No_solution _ . 
progress unfold dec_pb.
set_tac.
vm_compute in a.
unfold a in *;clear a.
unfold decompose in f.
unfold f in *;clear f.
set_tac.
vm_compute in a4; unfold a4 in *;clear a4.

vm_compute in f;unfold f in *;clear f.
match goal with 
  |- context C [a1 ?x] => 
    set (a4:=a1 x) in *
end.

set (h:=wf_lt_ms).
unfold a1,wf_lt_exc_pb_ok in a4.
vm_compute in a4.


(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "/home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/examples" "-I" "/home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/term_algebra" "-I" "/home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/term_orderings" "-I" "/home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/basis" "-I" "/home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/list_extensions" "-I" "/home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/examples/cime_trace/" "-I" "/home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/unification/") ***
*** compile-command: "coqc -I /home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/term_algebra -I /home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/term_orderings -I /home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/basis -I /home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/list_extensions -I /home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/examples/cime_trace/ -I /home/jforest/cvs_travail/a3pat/coccinelle/branches/v8.1/examples/  ./TRS/AG01/#3.12.trs.v" ***
*** End: ***
 *)
