 
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/basis".
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/list_extensions". 
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/term_algebra". 
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/term_orderings". 
Add LoadPath "/users/Sorin/Apps/coccinelle-8.2/examples/cime_trace".

Require terminaison.

Require Relations.

Require term.

Require List.

Require equational_theory.

Require rpo_extension.

Require equational_extension.

Require closure_extension.

Require term_extension.

Require dp.

Require Inclusion.

Require or_ext_generated.

Require ZArith.

Require ring_extention.

Require Zwf.

Require Inverse_Image.

Require matrix.

Require more_list_extention.

Require graph_dp.

Require subterm_dp.

Import List.

Import ZArith.

Set Implicit Arguments.

Module algebra.
 Module F
  <:term_spec.Signature.
  Inductive symb  :
   Set := 
     (* id_0 *)
    | id_0 : symb
     (* id__plus_ *)
    | id__plus_ : symb
     (* id_s *)
    | id_s : symb
     (* id__mult_ *)
    | id__mult_ : symb
  .
  
  
  Definition symb_eq_bool (f1 f2:symb) : bool := 
    match f1,f2 with
      | id_0,id_0 => true
      | id__plus_,id__plus_ => true
      | id_s,id_s => true
      | id__mult_,id__mult_ => true
      | _,_ => false
      end.
  
  
   (* Proof of decidability of equality over symb *)
  Definition symb_eq_bool_ok(f1 f2:symb) :
   match symb_eq_bool f1 f2 with
     | true => f1 = f2
     | false => f1 <> f2
     end.
  Proof.
    intros f1 f2.
    
    refine match f1 as u1,f2 as u2 return 
             match symb_eq_bool u1 u2 return 
               Prop with
               | true => u1 = u2
               | false => u1 <> u2
               end with
             | id_0,id_0 => refl_equal _
             | id__plus_,id__plus_ => refl_equal _
             | id_s,id_s => refl_equal _
             | id__mult_,id__mult_ => refl_equal _
             | _,_ => _
             end;intros abs;discriminate.
  Defined.
  
  
  Definition arity (f:symb) := 
    match f with
      | id_0 => term_spec.Free 0
      | id__plus_ => term_spec.Free 2
      | id_s => term_spec.Free 1
      | id__mult_ => term_spec.Free 2
      end.
  
  
  Definition symb_order (f1 f2:symb) : bool := 
    match f1,f2 with
      | id_0,id_0 => true
      | id_0,id__plus_ => false
      | id_0,id_s => false
      | id_0,id__mult_ => false
      | id__plus_,id_0 => true
      | id__plus_,id__plus_ => true
      | id__plus_,id_s => false
      | id__plus_,id__mult_ => false
      | id_s,id_0 => true
      | id_s,id__plus_ => true
      | id_s,id_s => true
      | id_s,id__mult_ => false
      | id__mult_,id_0 => true
      | id__mult_,id__plus_ => true
      | id__mult_,id_s => true
      | id__mult_,id__mult_ => true
      end.
  
  
  Module Symb.
   Definition A  := symb.
   
   Definition eq_A  := @eq A.
   
   
   Definition eq_proof : equivalence A eq_A.
   Proof.
     constructor.
     red ;reflexivity .
     red ;intros ;transitivity y ;assumption.
     red ;intros ;symmetry ;assumption.
   Defined.
   
   
   Add Relation A eq_A 
  reflexivity proved by (@equiv_refl _ _ eq_proof)
    symmetry proved by (@equiv_sym _ _ eq_proof)
      transitivity proved by (@equiv_trans _ _ eq_proof) as EQA
.
   
   Definition eq_bool  := symb_eq_bool.
   
   Definition eq_bool_ok  := symb_eq_bool_ok.
  End Symb.
  
  Export Symb.
 End F.
 
 Module Alg := term.Make'(F)(term_extension.IntVars).
 
 Module Alg_ext := term_extension.Make(Alg).
 
 Module EQT := equational_theory.Make(Alg).
 
 Module EQT_ext := equational_extension.Make(EQT).
End algebra.

Module R_peano_deep_rew.
 Inductive R_peano_rules  :
  algebra.Alg.term ->algebra.Alg.term ->Prop := 
    (* x+0 -> x *)
   | R_peano_rule_0 :
    R_peano_rules (algebra.Alg.Var 1) 
     (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Var 1)::
      (algebra.Alg.Term algebra.F.id_0 nil)::nil))
    (* x+s(y) -> s(x+y) *)
   | R_peano_rule_1 :
    R_peano_rules (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Term 
                   algebra.F.id__plus_ ((algebra.Alg.Var 1)::
                   (algebra.Alg.Var 2)::nil))::nil)) 
     (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Var 1)::
      (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Var 2)::nil))::nil))
    (* x  *0 -> 0 *)
   | R_peano_rule_2 :
    R_peano_rules (algebra.Alg.Term algebra.F.id_0 nil) 
     (algebra.Alg.Term algebra.F.id__mult_ ((algebra.Alg.Var 1)::
      (algebra.Alg.Term algebra.F.id_0 nil)::nil))
    (* x  *s(y) -> (x  *y)+x *)
   | R_peano_rule_3 :
    R_peano_rules (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Term 
                   algebra.F.id__mult_ ((algebra.Alg.Var 1)::
                   (algebra.Alg.Var 2)::nil))::(algebra.Alg.Var 1)::nil)) 
     (algebra.Alg.Term algebra.F.id__mult_ ((algebra.Alg.Var 1)::
      (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Var 2)::nil))::nil))
 .
 
 
 Definition R_peano_rule_as_list_0  := 
   ((algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Var 1)::
     (algebra.Alg.Term algebra.F.id_0 nil)::nil)),(algebra.Alg.Var 1))::
    nil.
 
 
 Definition R_peano_rule_as_list_1  := 
   ((algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Var 1)::
     (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Var 2)::nil))::nil)),
    (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Term algebra.F.id__plus_ 
     ((algebra.Alg.Var 1)::(algebra.Alg.Var 2)::nil))::nil)))::
    R_peano_rule_as_list_0.
 
 
 Definition R_peano_rule_as_list_2  := 
   ((algebra.Alg.Term algebra.F.id__mult_ ((algebra.Alg.Var 1)::
     (algebra.Alg.Term algebra.F.id_0 nil)::nil)),
    (algebra.Alg.Term algebra.F.id_0 nil))::R_peano_rule_as_list_1.
 
 
 Definition R_peano_rule_as_list_3  := 
   ((algebra.Alg.Term algebra.F.id__mult_ ((algebra.Alg.Var 1)::
     (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Var 2)::nil))::nil)),
    (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Term 
     algebra.F.id__mult_ ((algebra.Alg.Var 1)::(algebra.Alg.Var 2)::nil))::
     (algebra.Alg.Var 1)::nil)))::R_peano_rule_as_list_2.
 
 Definition R_peano_rule_as_list  := R_peano_rule_as_list_3.
 
 
 Lemma R_peano_rules_included :
  forall l r, R_peano_rules r l <-> In (l,r) R_peano_rule_as_list.
 Proof.
   intros l r.
   constructor.
   intros H.
   
   case H;clear H;
    (apply (more_list.mem_impl_in (@eq (algebra.Alg.term*algebra.Alg.term)));
     [tauto|idtac]);
    match goal with
      |  |- _ _ _ ?t ?l =>
       let u := fresh "u" in 
        (generalize (more_list.mem_bool_ok _ _ 
                      algebra.Alg_ext.eq_term_term_bool_ok t l);
          set (u:=more_list.mem_bool algebra.Alg_ext.eq_term_term_bool t l) in *;
          vm_compute in u|-;unfold u in *;clear u;intros H;refine H)
      end
    .
   intros H.
   vm_compute in H|-.
   rewrite  <- or_ext_generated.or5_equiv in H|-.
   case H;clear H;intros H.
   injection H;intros ;subst;constructor 4.
   injection H;intros ;subst;constructor 3.
   injection H;intros ;subst;constructor 2.
   injection H;intros ;subst;constructor 1.
   elim H.
 Qed.
 
 
 Lemma R_peano_non_var : forall x t, ~R_peano_rules t (algebra.EQT.T.Var x).
 Proof.
   intros x t H.
   inversion H.
 Qed.
 
 
 Lemma R_peano_reg :
  forall s t, 
   (R_peano_rules s t) ->
    forall x, In x (algebra.Alg.var_list s) ->In x (algebra.Alg.var_list t).
 Proof.
   intros s t H.
   
   inversion H;intros x Hx;
    (apply (more_list.mem_impl_in (@eq algebra.Alg.variable));[tauto|idtac]);
    apply (more_list.in_impl_mem (@eq algebra.Alg.variable)) in Hx;
    vm_compute in Hx|-*;tauto.
 Qed.
 
 Inductive and_2 (x5 x6:Prop) : Prop := 
   | conj_2 : x5->x6->and_2 x5 x6
 .
 
 
 Lemma are_constuctors_of_R_peano :
  forall t t', 
   (TransClosure.refl_trans_clos (algebra.EQT.one_step R_peano_rules) t' t) ->
    and_2 (t = (algebra.Alg.Term algebra.F.id_0 nil) ->
           t' = (algebra.Alg.Term algebra.F.id_0 nil)) 
     (forall x6, 
      t = (algebra.Alg.Term algebra.F.id_s (x6::nil)) ->
       exists x5,
         t' = (algebra.Alg.Term algebra.F.id_s (x5::nil))/\ 
         (TransClosure.refl_trans_clos (algebra.EQT.one_step R_peano_rules) 
           x5 x6)).
 Proof.
   intros t t' H.
   
   induction H as [|y IH z z_to_y] using 
   closure_extension.refl_trans_clos_ind2.
   constructor 1.
   intros H;intuition;constructor 1.
   intros x6 H;exists x6;intuition;constructor 1.
   inversion z_to_y as [t1 t2 H H0 H1|f l1 l2 H0 H H2];clear z_to_y;subst.
   
   inversion H as [t1 t2 sigma H2 H1 H0];clear H IH;subst;inversion H2;
    clear ;constructor;try (intros until 0 );clear ;intros abs;
    discriminate abs.
   destruct IH as [H_id_0 H_id_s].
   constructor.
   
   clear H_id_s;intros H;injection H;clear H;intros ;subst;
    repeat (
    match goal with
      | H:weaved_relation.one_step_list (algebra.EQT.one_step _) _ _ |- 
      _ => inversion H;clear H;subst
      end
    ).
   
   clear H_id_0;intros x6 H;injection H;clear H;intros ;subst;
    repeat (
    match goal with
      | H:weaved_relation.one_step_list (algebra.EQT.one_step _) _ _ |- 
      _ => inversion H;clear H;subst
      end
    ).
   
   match goal with
     | H:algebra.EQT.one_step _ ?y x6 |- _ =>
      destruct (H_id_s y (refl_equal _)) as [x5];intros ;intuition;exists x5;
       intuition;eapply closure_extension.refl_trans_clos_R;eassumption
     end
   .
 Qed.
 
 
 Lemma id_0_is_R_peano_constructor :
  forall t t', 
   (TransClosure.refl_trans_clos (algebra.EQT.one_step R_peano_rules) t' t) ->
    t = (algebra.Alg.Term algebra.F.id_0 nil) ->
     t' = (algebra.Alg.Term algebra.F.id_0 nil).
 Proof.
   intros t t' H.
   destruct (are_constuctors_of_R_peano H).
   assumption.
 Qed.
 
 
 Lemma id_s_is_R_peano_constructor :
  forall t t', 
   (TransClosure.refl_trans_clos (algebra.EQT.one_step R_peano_rules) t' t) ->
    forall x6, 
     t = (algebra.Alg.Term algebra.F.id_s (x6::nil)) ->
      exists x5,
        t' = (algebra.Alg.Term algebra.F.id_s (x5::nil))/\ 
        (TransClosure.refl_trans_clos (algebra.EQT.one_step R_peano_rules) 
          x5 x6).
 Proof.
   intros t t' H.
   destruct (are_constuctors_of_R_peano H).
   assumption.
 Qed.
 
 
 Ltac impossible_star_reduction_R_peano  :=
  match goal with
    | H:TransClosure.refl_trans_clos (algebra.EQT.one_step R_peano_rules) 
         _ (algebra.Alg.Term algebra.F.id_0 nil) |- _ =>
     let Heq := fresh "Heq" in 
      (set (Heq:=id_0_is_R_peano_constructor H (refl_equal _)) in *;
        (discriminate Heq)||
        (clearbody Heq;try (subst);try (clear Heq);clear H;
          impossible_star_reduction_R_peano ))
    | H:TransClosure.refl_trans_clos (algebra.EQT.one_step R_peano_rules) 
         _ (algebra.Alg.Term algebra.F.id_s (?x5::nil)) |- _ =>
     let x5 := fresh "x" in 
      (let Heq := fresh "Heq" in 
        (let Hred1 := fresh "Hred" in 
          (destruct (id_s_is_R_peano_constructor H (refl_equal _)) as 
           [x5 [Heq Hred1]];
            (discriminate Heq)||
            (injection Heq;intros ;subst;clear Heq;clear H;
              impossible_star_reduction_R_peano ))))
    end
  .
 
 
 Ltac simplify_star_reduction_R_peano  :=
  match goal with
    | H:TransClosure.refl_trans_clos (algebra.EQT.one_step R_peano_rules) 
         _ (algebra.Alg.Term algebra.F.id_0 nil) |- _ =>
     let Heq := fresh "Heq" in 
      (set (Heq:=id_0_is_R_peano_constructor H (refl_equal _)) in *;
        (discriminate Heq)||
        (clearbody Heq;try (subst);try (clear Heq);clear H;
          try (simplify_star_reduction_R_peano )))
    | H:TransClosure.refl_trans_clos (algebra.EQT.one_step R_peano_rules) 
         _ (algebra.Alg.Term algebra.F.id_s (?x5::nil)) |- _ =>
     let x5 := fresh "x" in 
      (let Heq := fresh "Heq" in 
        (let Hred1 := fresh "Hred" in 
          (destruct (id_s_is_R_peano_constructor H (refl_equal _)) as 
           [x5 [Heq Hred1]];
            (discriminate Heq)||
            (injection Heq;intros ;subst;clear Heq;clear H;
              try (simplify_star_reduction_R_peano )))))
    end
  .
End R_peano_deep_rew.

Module RpoLexAFS := rpo_extension.MakeRpoLexAFS(algebra.EQT).

Module RpoSdpMarkedAFS := rpo_extension.MakeRpoSdpMarkedAFS(algebra.EQT).

Module WF_R_peano_deep_rew.
 Inductive DP_R_peano  :
  algebra.Alg.term ->algebra.Alg.term ->Prop := 
    (* <x+s(y),x+y> *)
   | DP_R_peano_0 :
    DP_R_peano (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Var 1)::
                (algebra.Alg.Var 2)::nil)) 
     (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Var 1)::
      (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Var 2)::nil))::nil))
    (* <x  *s(y),(x  *y)+x> *)
   | DP_R_peano_1 :
    DP_R_peano (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Term 
                algebra.F.id__mult_ ((algebra.Alg.Var 1)::
                (algebra.Alg.Var 2)::nil))::(algebra.Alg.Var 1)::nil)) 
     (algebra.Alg.Term algebra.F.id__mult_ ((algebra.Alg.Var 1)::
      (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Var 2)::nil))::nil))
    (* <x  *s(y),x  *y> *)
   | DP_R_peano_2 :
    DP_R_peano (algebra.Alg.Term algebra.F.id__mult_ ((algebra.Alg.Var 1)::
                (algebra.Alg.Var 2)::nil)) 
     (algebra.Alg.Term algebra.F.id__mult_ ((algebra.Alg.Var 1)::
      (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Var 2)::nil))::nil))
 .
 
 Module ddp := dp.MakeDP(algebra.EQT).
 
 Module sdp :=  subterm_dp.MakeSubDP(algebra.EQT).
 
 
 
Ltac cdp_incl_dp_tac ind :=
  let H := fresh "H" in
  intros ?x ?y H;
  destruct H;
  match goal with
  |- sdp.Dp.dp _ ?t ?r =>
    match type of ind with
    | context f [_ ?l r -> _] =>
      match l with
      | context g [t] => 
        match eval vm_compute in
            (algebra.Alg.is_subterm_ok_true t l (refl_equal true)) with
        | exist _ ?pos ?Hpos => 
          constructor 1 with (p := pos) (t2 := l);
          [ constructor | exact Hpos | econstructor econstructor ]
        end
      end
    end
  end.
 
 
 Ltac destruct_nth_error_nth_subterm :=
  match goal with
    | H: context [List.nth_error _ ?i ] |- _ => 
      destruct i; simpl in *
    | H: context [algebra.Alg.subterm_at_pos _ ?p ] |- _ => 
      destruct p; simpl in *
    | H: Some _ = Some _ |- _ => 
      inversion H; clear H; subst; simpl in *
    | H: None = Some _ |- _ => 
      inversion H
    | H: Some _ <> None |- _ => 
      inversion H
    | H:algebra.EQT.defined _ ?f  |- _ => (* cons pas defini *)
      solve [
        let f := fresh "f" in 
          let l := fresh "l" in 
            let h1 := fresh "h" in 
              let h2 := fresh "h" in 
                inversion H as [f l h1 h2] ; subst;  inversion h2 ]
  end.
 
 
 Ltac destruct_until_absurd :=
  match goal with
    | |- context [List.nth_error _ ?i ] => 
      destruct i; simpl
    | |- context [algebra.Alg.subterm_at_pos _ ?p ] => 
      destruct p; simpl
    | |- Some _ <> Some _ => 
      let abs := fresh "abs" in
        solve [intro abs; inversion abs]
    | |- None <> Some _ => 
      let abs := fresh "abs" in
        solve [intro abs; inversion abs]
    | |- Some _ <> None => 
      let abs := fresh "abs" in
        solve [intro abs; inversion abs]
  end.
 
 
 
Lemma are_connected_incl : forall (R DP1 DP2:relation algebra.Alg.term) x y,
  (forall x y,DP1 x y -> DP2 x y) ->
  sdp.Dp.are_connected DP1 R x y
 -> sdp.Dp.are_connected DP2 R x y.
Proof.
  intros R DP1 DP2 x y H.
  destruct x; destruct y.
  unfold sdp.Dp.are_connected.
  intros [sigma [sigma' [hdp1 [hdp2 h]]]] .
  exists sigma; exists sigma';intros.
  split.
  apply H;assumption.
  split.
  apply H;assumption.
  assumption.  
Qed.
 
 
 Module WF_DP_R_peano.
  Inductive DP_R_peano_scc_0  :
   algebra.Alg.term ->algebra.Alg.term ->Prop := 
     (* <x+s(y),x+y> *)
    | DP_R_peano_scc_0_0 :
     DP_R_peano_scc_0 (algebra.Alg.Term algebra.F.id__plus_ 
                       ((algebra.Alg.Var 1)::(algebra.Alg.Var 2)::nil)) 
      (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Var 1)::
       (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Var 2)::nil))::nil))
  .
  
  
  Module WF_DP_R_peano_scc_0.
   Definition prec (f:algebra.F.symb) := 
     match f with
       | algebra.F.id__mult_ => 5
       | algebra.F.id__plus_ => 3
       | algebra.F.id_s => 2
       | algebra.F.id_0 => 0
       end.
   
   Definition prec_marked (f:algebra.F.symb) := 
     match f with
       | algebra.F.id__plus_ => 4
       | algebra.F.id__mult_ => 1
       | _ => 6
       end.
   
   
   Definition status (f:algebra.F.symb) := 
     match f with
       | algebra.F.id_0 => rpo.Lex
       | algebra.F.id__plus_ => rpo.Lex
       | algebra.F.id_s => rpo.Lex
       | algebra.F.id__mult_ => rpo.Lex
       end.
   
   Definition status_marked (f:algebra.F.symb) := 
     match f with
       | algebra.F.id__mult_ => rpo.Lex
       | algebra.F.id__plus_ => rpo.Lex
       | _ => rpo.Lex
       end.
   
   
   Definition afs (f:algebra.F.symb) := 
     match f with
       | algebra.F.id_0 => RpoSdpMarkedAFS.Afs.AFS_id algebra.F.id_0
       | algebra.F.id__plus_ =>
        RpoSdpMarkedAFS.Afs.AFS_id algebra.F.id__plus_
       | algebra.F.id_s => RpoSdpMarkedAFS.Afs.AFS_id algebra.F.id_s
       | algebra.F.id__mult_ =>
        RpoSdpMarkedAFS.Afs.AFS_id algebra.F.id__mult_
       end.
   
   Definition afs_marked (f:algebra.F.symb) := 
     match f with
       | algebra.F.id__mult_ =>
        RpoSdpMarkedAFS.Afs.AFS_id algebra.F.id__mult_
       | algebra.F.id__plus_ =>
        RpoSdpMarkedAFS.Afs.AFS_id algebra.F.id__plus_
       | _ => RpoSdpMarkedAFS.Afs.AFS_id f
       end.
   
   
   Lemma wf :
    well_founded (WF_R_peano_deep_rew.sdp.Rcdp_min R_peano_deep_rew.R_peano_rules 
                   WF_DP_R_peano.DP_R_peano_scc_0).
   Proof.
     RpoSdpMarkedAFS.prove_wf 2 prec status afs prec_marked status_marked 
     afs_marked.
   Qed.
  End WF_DP_R_peano_scc_0.
  
  Definition wf_DP_R_peano_scc_0  := WF_DP_R_peano_scc_0.wf.
  
  
  Lemma acc_DP_R_peano_scc_0 :
   forall x sigma, 
    In x (List.map (algebra.Alg.apply_subst sigma) 
           ((algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Var 1)::
             (algebra.Alg.Var 2)::nil))::nil)) ->
     Acc (sdp.Rcdp_min R_peano_deep_rew.R_peano_rules 
           WF_R_peano_deep_rew.DP_R_peano) x.
  Proof.
    intros x.
    pattern x.
    apply well_founded_induction with (1:=wf_DP_R_peano_scc_0) .
    clear .
    intros x IH sigma H0.
    simpl in H0|-.
    
    constructor;intros y Hy;inversion Hy;clear Hy;subst;destruct H;
     inversion H2;clear H2;subst;revert H3 H1;destruct H5;intros H3 H1;
     match goal with
       |  |- Acc _ 
              (algebra.Alg.apply_subst ?sigma 
                (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Var 1)::
                 (algebra.Alg.Var 2)::nil))) =>
        (apply IH with sigma;
         [(constructor;
           [(constructor 1 with l2;[assumption|rewrite  <- H3]);
             constructor constructor|assumption])|
         apply in_map;
          (rewrite (algebra.EQT_ext.inb_equiv _ algebra.Alg.eq_bool);
           [vm_compute in |-*;refine (refl_equal _)|
           apply algebra.Alg_ext.term_eq_bool_equiv])])
       |  |- _ =>
        simpl in H0|-;injection H3;clear H3;intros ;subst;
         repeat (
         match type of H0 with
           | or _ _ => destruct H0 as [H0| H0]
           | False => elim H0
           end
         );
         (discriminate H0)||
         (injection H0;clear H0;intros ;subst;
           repeat (
           match goal with
             | H:TransClosure.refl_trans_clos (weaved_relation.one_step_list _) _ _
                   |- _ =>
              destruct (algebra.EQT_ext.cons_star _ _ _ _ _ H) ;clear H
             end
           );R_peano_deep_rew.impossible_star_reduction_R_peano )
       end
     .
  Qed.
  
  
  Inductive DP_R_peano_non_scc_0  :
   algebra.Alg.term ->algebra.Alg.term ->Prop := 
     (* <x  *s(y),(x  *y)+x> *)
    | DP_R_peano_non_scc_0_0 :
     DP_R_peano_non_scc_0 (algebra.Alg.Term algebra.F.id__plus_ 
                           ((algebra.Alg.Term algebra.F.id__mult_ 
                           ((algebra.Alg.Var 1)::(algebra.Alg.Var 2)::nil))::
                           (algebra.Alg.Var 1)::nil)) 
      (algebra.Alg.Term algebra.F.id__mult_ ((algebra.Alg.Var 1)::
       (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Var 2)::nil))::nil))
  .
  
  
  Lemma acc_DP_R_peano_non_scc_0 :
   forall x sigma, 
    In x (List.map (algebra.Alg.apply_subst sigma) 
           ((algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Term 
             algebra.F.id__mult_ ((algebra.Alg.Var 1)::
             (algebra.Alg.Var 2)::nil))::(algebra.Alg.Var 1)::nil))::
            nil)) ->
     Acc (sdp.Rcdp_min R_peano_deep_rew.R_peano_rules 
           WF_R_peano_deep_rew.DP_R_peano) x.
  Proof.
    intros x sigma H0.
    simpl in H0|-.
    
    constructor;intros y Hy;inversion Hy;clear Hy;subst;destruct H;
     inversion H2;clear H2;subst;revert H3 H1;destruct H5;intros H3 H1;
     match goal with
       |  |- Acc _ 
              (algebra.Alg.apply_subst ?sigma 
                (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Var 1)::
                 (algebra.Alg.Var 2)::nil))) =>
        apply acc_DP_R_peano_scc_0 with sigma;apply in_map;
         (rewrite (algebra.EQT_ext.inb_equiv _ algebra.Alg.eq_bool);
          [vm_compute in |-*;refine (refl_equal _)|
          apply algebra.Alg_ext.term_eq_bool_equiv])
       |  |- _ =>
        simpl in H0|-;injection H3;clear H3;intros ;subst;
         repeat (
         match type of H0 with
           | or _ _ => destruct H0 as [H0| H0]
           | False => elim H0
           end
         );
         (discriminate H0)||
         (injection H0;clear H0;intros ;subst;
           repeat (
           match goal with
             | H:TransClosure.refl_trans_clos (weaved_relation.one_step_list _) _ _
                   |- _ =>
              destruct (algebra.EQT_ext.cons_star _ _ _ _ _ H) ;clear H
             end
           );R_peano_deep_rew.impossible_star_reduction_R_peano )
       end
     .
  Qed.
  
  
  Inductive DP_R_peano_scc_1  :
   algebra.Alg.term ->algebra.Alg.term ->Prop := 
     (* <x  *s(y),x  *y> *)
    | DP_R_peano_scc_1_0 :
     DP_R_peano_scc_1 (algebra.Alg.Term algebra.F.id__mult_ 
                       ((algebra.Alg.Var 1)::(algebra.Alg.Var 2)::nil)) 
      (algebra.Alg.Term algebra.F.id__mult_ ((algebra.Alg.Var 1)::
       (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Var 2)::nil))::nil))
  .
  
  
  Module WF_DP_R_peano_scc_1.
   Definition prec (f:algebra.F.symb) := 
     match f with
       | algebra.F.id__mult_ => 5
       | algebra.F.id__plus_ => 3
       | algebra.F.id_s => 2
       | algebra.F.id_0 => 0
       end.
   
   Definition prec_marked (f:algebra.F.symb) := 
     match f with
       | algebra.F.id__plus_ => 4
       | algebra.F.id__mult_ => 1
       | _ => 6
       end.
   
   
   Definition status (f:algebra.F.symb) := 
     match f with
       | algebra.F.id_0 => rpo.Lex
       | algebra.F.id__plus_ => rpo.Lex
       | algebra.F.id_s => rpo.Lex
       | algebra.F.id__mult_ => rpo.Lex
       end.
   
   Definition status_marked (f:algebra.F.symb) := 
     match f with
       | algebra.F.id__mult_ => rpo.Lex
       | algebra.F.id__plus_ => rpo.Lex
       | _ => rpo.Lex
       end.
   
   
   Definition afs (f:algebra.F.symb) := 
     match f with
       | algebra.F.id_0 => RpoSdpMarkedAFS.Afs.AFS_id algebra.F.id_0
       | algebra.F.id__plus_ =>
        RpoSdpMarkedAFS.Afs.AFS_id algebra.F.id__plus_
       | algebra.F.id_s => RpoSdpMarkedAFS.Afs.AFS_id algebra.F.id_s
       | algebra.F.id__mult_ =>
        RpoSdpMarkedAFS.Afs.AFS_id algebra.F.id__mult_
       end.
   
   Definition afs_marked (f:algebra.F.symb) := 
     match f with
       | algebra.F.id__mult_ =>
        RpoSdpMarkedAFS.Afs.AFS_id algebra.F.id__mult_
       | algebra.F.id__plus_ =>
        RpoSdpMarkedAFS.Afs.AFS_id algebra.F.id__plus_
       | _ => RpoSdpMarkedAFS.Afs.AFS_id f
       end.
   
   
   Lemma wf :
    well_founded (WF_R_peano_deep_rew.sdp.Rcdp_min R_peano_deep_rew.R_peano_rules 
                   WF_DP_R_peano.DP_R_peano_scc_1).
   Proof.
     RpoSdpMarkedAFS.prove_wf 2 prec status afs prec_marked status_marked 
     afs_marked.
   Qed.
  End WF_DP_R_peano_scc_1.
  
  Definition wf_DP_R_peano_scc_1  := WF_DP_R_peano_scc_1.wf.
  
  
  Lemma acc_DP_R_peano_scc_1 :
   forall x sigma, 
    In x (List.map (algebra.Alg.apply_subst sigma) 
           ((algebra.Alg.Term algebra.F.id__mult_ ((algebra.Alg.Var 1)::
             (algebra.Alg.Var 2)::nil))::nil)) ->
     Acc (sdp.Rcdp_min R_peano_deep_rew.R_peano_rules 
           WF_R_peano_deep_rew.DP_R_peano) x.
  Proof.
    intros x.
    pattern x.
    apply well_founded_induction with (1:=wf_DP_R_peano_scc_1) .
    clear .
    intros x IH sigma H0.
    simpl in H0|-.
    
    constructor;intros y Hy;inversion Hy;clear Hy;subst;destruct H;
     inversion H2;clear H2;subst;revert H3 H1;destruct H5;intros H3 H1;
     match goal with
       |  |- Acc _ 
              (algebra.Alg.apply_subst ?sigma 
                (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Term 
                 algebra.F.id__mult_ ((algebra.Alg.Var 1)::
                 (algebra.Alg.Var 2)::nil))::(algebra.Alg.Var 1)::nil))) =>
        apply acc_DP_R_peano_non_scc_0 with sigma;apply in_map;
         (rewrite (algebra.EQT_ext.inb_equiv _ algebra.Alg.eq_bool);
          [vm_compute in |-*;refine (refl_equal _)|
          apply algebra.Alg_ext.term_eq_bool_equiv])
       |  |- Acc _ 
              (algebra.Alg.apply_subst ?sigma 
                (algebra.Alg.Term algebra.F.id__mult_ ((algebra.Alg.Var 1)::
                 (algebra.Alg.Var 2)::nil))) =>
        (apply IH with sigma;
         [(constructor;
           [(constructor 1 with l2;[assumption|rewrite  <- H3]);
             constructor constructor|assumption])|
         apply in_map;
          (rewrite (algebra.EQT_ext.inb_equiv _ algebra.Alg.eq_bool);
           [vm_compute in |-*;refine (refl_equal _)|
           apply algebra.Alg_ext.term_eq_bool_equiv])])
       |  |- _ =>
        simpl in H0|-;injection H3;clear H3;intros ;subst;
         repeat (
         match type of H0 with
           | or _ _ => destruct H0 as [H0| H0]
           | False => elim H0
           end
         );
         (discriminate H0)||
         (injection H0;clear H0;intros ;subst;
           repeat (
           match goal with
             | H:TransClosure.refl_trans_clos (weaved_relation.one_step_list _) _ _
                   |- _ =>
              destruct (algebra.EQT_ext.cons_star _ _ _ _ _ H) ;clear H
             end
           );R_peano_deep_rew.impossible_star_reduction_R_peano )
       end
     .
  Qed.
  
  
  Lemma wf :
   well_founded (sdp.Rcdp_min R_peano_deep_rew.R_peano_rules DP_R_peano).
  Proof.
    constructor;intros y Hy;inversion Hy;clear Hy;subst;destruct H;
     inversion H1;clear H1;subst;revert H2 H0;case H4;intros H2 H0;
     match goal with
       |  |- Acc _ 
              (algebra.Alg.apply_subst ?sigma 
                (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Var 1)::
                 (algebra.Alg.Var 2)::nil))) =>
        apply acc_DP_R_peano_scc_0 with sigma;apply in_map;
         (rewrite (algebra.EQT_ext.inb_equiv _ algebra.Alg.eq_bool);
          [vm_compute in |-*;refine (refl_equal _)|
          apply algebra.Alg_ext.term_eq_bool_equiv])
       |  |- Acc _ 
              (algebra.Alg.apply_subst ?sigma 
                (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Term 
                 algebra.F.id__mult_ ((algebra.Alg.Var 1)::
                 (algebra.Alg.Var 2)::nil))::(algebra.Alg.Var 1)::nil))) =>
        apply acc_DP_R_peano_non_scc_0 with sigma;apply in_map;
         (rewrite (algebra.EQT_ext.inb_equiv _ algebra.Alg.eq_bool);
          [vm_compute in |-*;refine (refl_equal _)|
          apply algebra.Alg_ext.term_eq_bool_equiv])
       |  |- Acc _ 
              (algebra.Alg.apply_subst ?sigma 
                (algebra.Alg.Term algebra.F.id__mult_ ((algebra.Alg.Var 1)::
                 (algebra.Alg.Var 2)::nil))) =>
        apply acc_DP_R_peano_scc_1 with sigma;apply in_map;
         (rewrite (algebra.EQT_ext.inb_equiv _ algebra.Alg.eq_bool);
          [vm_compute in |-*;refine (refl_equal _)|
          apply algebra.Alg_ext.term_eq_bool_equiv])
       |  |- _ =>
        injection H;clear H;intros ;subst;
         repeat (
         match goal with
           | H:TransClosure.refl_trans_clos (weaved_relation.one_step_list _) _ _
                 |- _ =>
            destruct (algebra.EQT_ext.cons_star _ _ _ _ _ H) ;clear H
           end
         );R_peano_deep_rew.impossible_star_reduction_R_peano 
       end
     .
  Qed.
 End WF_DP_R_peano.
 
 Ltac destruct_until_cdp_or_notdefined :=
  match goal with
    | H: None = Some _ |- _ => inversion H
    | H:algebra.EQT.defined _ ?f |- _ =>
      solve [inversion H;
        match goal with
          H': R_peano_deep_rew.R_peano_rules _ _ |- _ => 
            inversion H'
        end 
        | solve
          [constructor; constructor |
            constructor 2; constructor ; constructor |
              constructor 2 ;constructor 2; constructor |
              constructor 2 ;constructor 2; constructor 2 ]
      ]
    | H: Some _ = Some _ |- _ =>
      inversion H; clear H;subst
    | H: (match (nth_error _ ?n) with
            Some _ => _
            | None => _ end) = Some _ |- _  => 
    destruct n;simpl in *
    | H: algebra.Alg.subterm_at_pos _ ?p = Some _ |- _ => destruct p;simpl in *
  end.
 
 Definition wf_H  := WF_DP_R_peano.wf.
 
 Lemma wf :
  well_founded (algebra.EQT.one_step R_peano_deep_rew.R_peano_rules).
 Proof.
   apply sdp.Dp.ddp_criterion.
  intros x t .
   apply R_peano_deep_rew.R_peano_non_var.
   apply R_peano_deep_rew.R_peano_reg.
   
   intros ;
    apply (ddp.constructor_defined_dec _ _ 
            R_peano_deep_rew.R_peano_rules_included).
   
   
  apply Inclusion.wf_incl with (2:=wf_H). 
  intros x y.
  clear;intros H;destruct H;constructor;[|assumption].
    inversion H. econstructor; try eassumption;subst.
  inversion H2. constructor. 
 clear -H5.
  apply sdp.Dp.ddp_list_is_complete with (is_def := algebra.EQT_ext.is_def (sdp.Dp.defined_list R_peano_deep_rew.R_peano_rule_as_list nil)) (1:=R_peano_deep_rew.R_peano_rules_included) in H5.
  vm_compute in H5;
  repeat (destruct H5 as [H5|H5]; [ injection H5;clear H5;intros;subst;constructor|]);
    elim H5.

  apply algebra.EQT_ext.is_def_equiv.
  split.
  apply sdp.Dp.defined_list_sound with (1:=R_peano_deep_rew.R_peano_rules_included). 
  apply sdp.Dp.defined_list_complete with (1:=R_peano_deep_rew.R_peano_rules_included)
 .
 Qed.
End WF_R_peano_deep_rew.

Definition prec_s := RpoLexAFS.P.

Definition t1_s :=  (algebra.Alg.Var 1).

Definition t0_s := (algebra.Alg.Term algebra.F.id_0 nil).

Definition tsx_s := (algebra.Alg.Term algebra.F.id_s ((algebra.Alg.Var 1)::nil)).

Eval compute in (rpo.rpo_eval prec_s 9 t1_s t2_s).     

Eval compute in (RpoLexAFS.Rpo.rpo_eval prec_s 9 t0_s tsx_s).



Definition t2_s := (algebra.Alg.Term algebra.F.id__plus_ ((algebra.Alg.Var 1)::
      (algebra.Alg.Term algebra.F.id_0 nil)::nil)).
 
rpo.rpo_eval prec_s 9 t1_s t2_s.

RpoLexAFS.Rpo.rpo prec_s 9 (RpoLexAFS (afs t1_s) (afs t2_s)).