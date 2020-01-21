
Require Import tree_list_spec.



Definition type_LF_14 :=  nat ->  nat ->  tree ->  tree -> (Prop * (List.list term)).

Definition F_14 : type_LF_14:= (fun   u1 _ u2 _ => ((flat (ins u1 u2)) = (Cons u1 (flat u2)), (Term id_flat ((Term id_ins ((model_nat u1):: (model_tree u2)::nil))::nil))::(Term id_Cons ((model_nat u1):: (Term id_flat ((model_tree u2)::nil))::nil))::nil)).
Definition F_24 : type_LF_14:= (fun   u1 u4  _ _ => ((flat (Noeud (Feuille u1) (Feuille u4))) = (Cons u1 (flat (Feuille u4))), (Term id_flat ((Term id_Noeud ((Term id_Feuille ((model_nat u1)::nil)):: (Term id_Feuille ((model_nat u4)::nil))::nil))::nil))::(Term id_Cons ((model_nat u1):: (Term id_flat ((Term id_Feuille ((model_nat u4)::nil))::nil))::nil))::nil)).
Definition F_30 : type_LF_14:= (fun   u1 _ u4 u5 => ((flat (Noeud (ins u1 u4) u5)) = (Cons u1 (flat (Noeud u4 u5))), (Term id_flat ((Term id_Noeud ((Term id_ins ((model_nat u1):: (model_tree u4)::nil)):: (model_tree u5)::nil))::nil))::(Term id_Cons ((model_nat u1):: (Term id_flat ((Term id_Noeud ((model_tree u4):: (model_tree u5)::nil))::nil))::nil))::nil)).
Definition F_36 : type_LF_14:= (fun   u1 u4  _ _ => ((app (flat (Feuille u1)) (flat (Feuille u4))) = (Cons u1 (flat (Feuille u4))), (Term id_app ((Term id_flat ((Term id_Feuille ((model_nat u1)::nil))::nil)):: (Term id_flat ((Term id_Feuille ((model_nat u4)::nil))::nil))::nil))::(Term id_Cons ((model_nat u1):: (Term id_flat ((Term id_Feuille ((model_nat u4)::nil))::nil))::nil))::nil)).
Definition F_40 : type_LF_14:= (fun   u1 _ u4 u5 => ((app (flat (ins u1 u4)) (flat u5)) = (Cons u1 (flat (Noeud u4 u5))), (Term id_app ((Term id_flat ((Term id_ins ((model_nat u1):: (model_tree u4)::nil))::nil)):: (Term id_flat ((model_tree u5)::nil))::nil))::(Term id_Cons ((model_nat u1):: (Term id_flat ((Term id_Noeud ((model_tree u4):: (model_tree u5)::nil))::nil))::nil))::nil)).
Definition F_45 : type_LF_14:= (fun   u1 u4  _ _ => ((app (Cons u1 Nil) (flat (Feuille u4))) = (Cons u1 (flat (Feuille u4))), (Term id_app ((Term id_Cons ((model_nat u1):: (Term id_Nil nil)::nil)):: (Term id_flat ((Term id_Feuille ((model_nat u4)::nil))::nil))::nil))::(Term id_Cons ((model_nat u1):: (Term id_flat ((Term id_Feuille ((model_nat u4)::nil))::nil))::nil))::nil)).
Definition F_50 : type_LF_14:= (fun   u1 _ u4 u5 => ((app (Cons u1 (flat u4)) (flat u5)) = (Cons u1 (flat (Noeud u4 u5))), (Term id_app ((Term id_Cons ((model_nat u1):: (Term id_flat ((model_tree u4)::nil))::nil)):: (Term id_flat ((model_tree u5)::nil))::nil))::(Term id_Cons ((model_nat u1):: (Term id_flat ((Term id_Noeud ((model_tree u4):: (model_tree u5)::nil))::nil))::nil))::nil)).
Definition F_56 : type_LF_14:= (fun   u1 u4  _ _ => ((app (Cons u1 Nil) (Cons u4 Nil)) = (Cons u1 (flat (Feuille u4))), (Term id_app ((Term id_Cons ((model_nat u1):: (Term id_Nil nil)::nil)):: (Term id_Cons ((model_nat u4):: (Term id_Nil nil)::nil))::nil))::(Term id_Cons ((model_nat u1):: (Term id_flat ((Term id_Feuille ((model_nat u4)::nil))::nil))::nil))::nil)).
Definition F_61 : type_LF_14:= (fun   u1 _ u4 u5 => ((app (Cons u1 (flat u4)) (flat u5)) = (Cons u1 (app (flat u4) (flat u5))), (Term id_app ((Term id_Cons ((model_nat u1):: (Term id_flat ((model_tree u4)::nil))::nil)):: (Term id_flat ((model_tree u5)::nil))::nil))::(Term id_Cons ((model_nat u1):: (Term id_app ((Term id_flat ((model_tree u4)::nil)):: (Term id_flat ((model_tree u5)::nil))::nil))::nil))::nil)).
Definition F_70 : type_LF_14:= (fun   u1 _ u4 u5 => ((Cons u1 (app (flat u4) (flat u5))) = (Cons u1 (app (flat u4) (flat u5))), (Term id_Cons ((model_nat u1):: (Term id_app ((Term id_flat ((model_tree u4)::nil)):: (Term id_flat ((model_tree u5)::nil))::nil))::nil))::(Term id_Cons ((model_nat u1):: (Term id_app ((Term id_flat ((model_tree u4)::nil)):: (Term id_flat ((model_tree u5)::nil))::nil))::nil))::nil)).
Definition F_66 : type_LF_14:= (fun   u1 u4  _ _ => ((app (Cons u1 Nil) (Cons u4 Nil)) = (Cons u1 (Cons u4 Nil)), (Term id_app ((Term id_Cons ((model_nat u1):: (Term id_Nil nil)::nil)):: (Term id_Cons ((model_nat u4):: (Term id_Nil nil)::nil))::nil))::(Term id_Cons ((model_nat u1):: (Term id_Cons ((model_nat u4):: (Term id_Nil nil)::nil))::nil))::nil)).
Definition F_73 : type_LF_14:= (fun   u1 u4  _ _ => ((Cons u1 (app Nil (Cons u4 Nil))) = (Cons u1 (Cons u4 Nil)), (Term id_Cons ((model_nat u1):: (Term id_app ((Term id_Nil nil):: (Term id_Cons ((model_nat u4):: (Term id_Nil nil)::nil))::nil))::nil))::(Term id_Cons ((model_nat u1):: (Term id_Cons ((model_nat u4):: (Term id_Nil nil)::nil))::nil))::nil)).
Definition F_75 : type_LF_14:= (fun   u1 _  _ _ => (u1 = u1, (model_nat u1)::(model_nat u1)::nil)).
Definition F_76 : type_LF_14:= (fun   u4 _  _ _ => ((app Nil (Cons u4 Nil)) = (Cons u4 Nil), (Term id_app ((Term id_Nil nil):: (Term id_Cons ((model_nat u4):: (Term id_Nil nil)::nil))::nil))::(Term id_Cons ((model_nat u4):: (Term id_Nil nil)::nil))::nil)).
Definition F_80 : type_LF_14:= (fun   u4 _  _ _ => ((Cons u4 Nil) = (Cons u4 Nil), (Term id_Cons ((model_nat u4):: (Term id_Nil nil)::nil))::(Term id_Cons ((model_nat u4):: (Term id_Nil nil)::nil))::nil)).

Definition LF_14 := [F_14, F_24, F_30, F_36, F_40, F_45, F_50, F_56, F_61, F_70, F_66, F_73, F_75, F_76, F_80].


Function f_14 (u2: tree) (u1: nat) {struct u2} : tree :=
 match u2, u1 with
| (Feuille u4), _ => (Feuille 0 )
| (Noeud u4 u5), _ => (Feuille 0 )
end.

Lemma main_14 : forall F, In F LF_14 -> forall u1, forall u2, forall u3, forall u4, (forall F', In F' LF_14 -> forall e1, forall e2, forall e3, forall e4, less (snd (F' e1 e2 e3 e4)) (snd (F u1 u2 u3 u4)) -> fst (F' e1 e2 e3 e4)) -> fst (F u1 u2 u3 u4).
Proof.
intros F HF u1 u2 u3 u4; case_In HF; intro Hind.

	(* GENERATE on [ 14 ] *)

rename u1 into _u1. rename u2 into d_u2. rename u3 into _u2. rename u4 into d_u4. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u2, u1, (f_14 u2 u1). apply f_14_ind.

(* case [ 24 ] *)

intros _u2 _u1. intro u4.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_24). clear HFabs0.
assert (HFabs0 : fst (F_24 _u1 u4 (Feuille 0 ) (Feuille 0 ))).
apply Hind. trivial_in 1. unfold snd. unfold F_24. unfold F_14. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_14. unfold F_24.
auto.


(* case [ 30 ] *)

intros _u2 _u1. intro u4. intro u5.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_30). clear HFabs0.
assert (HFabs0 : fst (F_30 _u1 0 u4 u5)).
apply Hind. trivial_in 2. unfold snd. unfold F_30. unfold F_14. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_14. unfold F_30.
auto.





	(* REWRITING on [ 24 ] *)

rename u1 into _u1. rename u2 into _u4. rename u3 into d_u3. rename u4 into d_u4. 
rename _u1 into u1. rename _u4 into u4. 
assert (Res := Hind F_36). clear Hind.
assert (HFabs1 : fst (F_36 u1 u4 (Feuille 0 ) (Feuille 0 ))).
apply Res. trivial_in 3. unfold snd. unfold F_36. unfold F_24. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_24. unfold fst in HFabs1. unfold F_36 in HFabs1.   
pattern (Feuille u1), (Feuille u4). simpl (flat _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 30 ] *)

rename u1 into _u1. rename u2 into d_u2. rename u3 into _u4. rename u4 into _u5. 
rename _u1 into u1. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_40). clear Hind.
assert (HFabs1 : fst (F_40 u1 0 u4 u5)).
apply Res. trivial_in 4. unfold snd. unfold F_40. unfold F_30. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_30. unfold fst in HFabs1. unfold F_40 in HFabs1.   
pattern (ins u1 u4), u5. simpl (flat _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 36 ] *)

rename u1 into _u1. rename u2 into _u4. rename u3 into d_u3. rename u4 into d_u4. 
rename _u1 into u1. rename _u4 into u4. 
assert (Res := Hind F_45). clear Hind.
assert (HFabs1 : fst (F_45 u1 u4 (Feuille 0 ) (Feuille 0 ))).
apply Res. trivial_in 5. unfold snd. unfold F_45. unfold F_36. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_36. unfold fst in HFabs1. unfold F_45 in HFabs1.   
pattern u1. simpl (flat _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 40 ] *)

rename u1 into _u1. rename u2 into d_u2. rename u3 into _u4. rename u4 into _u5. 
rename _u1 into u1. rename _u4 into u4. rename _u5 into u5. 
assert (H := Hind F_14).
assert (Res := Hind F_50). clear Hind.
assert (HFabs0 : fst (F_14 u1 0 u4 (Feuille 0 ))).
apply H. trivial_in 0. unfold snd. unfold F_14. unfold F_40. rewrite_model. abstract solve_rpo_mul.
unfold fst in HFabs0. unfold F_14 in HFabs0. simpl in HFabs0.

assert (HFabs1 : fst (F_50 u1 0 u4 u5)).
apply Res. trivial_in 6. unfold snd. unfold F_50. unfold F_40. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_40. unfold fst in HFabs1. unfold F_50 in HFabs1.   
pattern u1, u4. simpl (flat _). cbv beta.
try rewrite  HFabs0.  simpl. auto.



	(* REWRITING on [ 45 ] *)

rename u1 into _u1. rename u2 into _u4. rename u3 into d_u3. rename u4 into d_u4. 
rename _u1 into u1. rename _u4 into u4. 
assert (Res := Hind F_56). clear Hind.
assert (HFabs1 : fst (F_56 u1 u4 (Feuille 0 ) (Feuille 0 ))).
apply Res. trivial_in 7. unfold snd. unfold F_56. unfold F_45. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_45. unfold fst in HFabs1. unfold F_56 in HFabs1.   
pattern u4. simpl (flat _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 50 ] *)

rename u1 into _u1. rename u2 into d_u2. rename u3 into _u4. rename u4 into _u5. 
rename _u1 into u1. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_61). clear Hind.
assert (HFabs1 : fst (F_61 u1 0 u4 u5)).
apply Res. trivial_in 8. unfold snd. unfold F_61. unfold F_50. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_50. unfold fst in HFabs1. unfold F_61 in HFabs1.   
pattern u4, u5. simpl (flat _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 56 ] *)

rename u1 into _u1. rename u2 into _u4. rename u3 into d_u3. rename u4 into d_u4. 
rename _u1 into u1. rename _u4 into u4. 
assert (Res := Hind F_66). clear Hind.
assert (HFabs1 : fst (F_66 u1 u4 (Feuille 0 ) (Feuille 0 ))).
apply Res. trivial_in 10. unfold snd. unfold F_66. unfold F_56. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_56. unfold fst in HFabs1. unfold F_66 in HFabs1.   
pattern u4. simpl (flat _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 61 ] *)

rename u1 into _u1. rename u2 into d_u2. rename u3 into _u4. rename u4 into _u5. 
rename _u1 into u1. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_70). clear Hind.
assert (HFabs1 : fst (F_70 u1 0 u4 u5)).
apply Res. trivial_in 9. unfold snd. unfold F_70. unfold F_61. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_61. unfold fst in HFabs1. unfold F_70 in HFabs1.   
pattern u1, (flat u4), (flat u5). simpl (app _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 70 ] *)

unfold fst. unfold F_70.
auto.



	(* REWRITING on [ 66 ] *)

rename u1 into _u1. rename u2 into _u4. rename u3 into d_u3. rename u4 into d_u4. 
rename _u1 into u1. rename _u4 into u4. 
assert (Res := Hind F_73). clear Hind.
assert (HFabs1 : fst (F_73 u1 u4 (Feuille 0 ) (Feuille 0 ))).
apply Res. trivial_in 11. unfold snd. unfold F_73. unfold F_66. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_66. unfold fst in HFabs1. unfold F_73 in HFabs1.   
pattern u1, Nil, (Cons u4 Nil). simpl (app _ _). cbv beta.
 simpl. auto.



	(* POSITIVE DECOMPOSITION on [ 73 ] *)

rename u1 into _u1. rename u2 into _u4. rename u3 into d_u3. rename u4 into d_u4. 
rename _u1 into u1. rename _u4 into u4. 
assert (H2 := Hind F_75). 
assert (HFabs2 : fst (F_75 u1 0 (Feuille 0 ) (Feuille 0 ))).
apply H2. trivial_in 12. unfold snd. unfold F_75. unfold F_73. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_73. unfold F_75.

unfold fst in HFabs2. unfold F_75 in HFabs2.



assert (H1 := Hind F_76). 
assert (HFabs1 : fst (F_76 u4 0 (Feuille 0 ) (Feuille 0 ))).
apply H1. trivial_in 13. unfold snd. unfold F_76. unfold F_73. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_73. unfold F_76.

unfold fst in HFabs1. unfold F_76 in HFabs1.

repeat (auto || (rewrite HFabs2|| rewrite HFabs1||  auto)).


	(* TAUTOLOGY on [ 75 ] *)

unfold fst. unfold F_75.
auto.



	(* REWRITING on [ 76 ] *)

rename u1 into _u4. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. 
rename _u4 into u4. 
assert (Res := Hind F_80). clear Hind.
assert (HFabs1 : fst (F_80 u4 0 (Feuille 0 ) (Feuille 0 ))).
apply Res. trivial_in 14. unfold snd. unfold F_80. unfold F_76. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_76. unfold fst in HFabs1. unfold F_80 in HFabs1.   
pattern (Cons u4 Nil). simpl (app _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 80 ] *)

unfold fst. unfold F_80.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_14 := fun f => exists F, In F LF_14 /\ exists e1, exists e2, exists e3, exists e4, f = F e1 e2 e3 e4.

Theorem all_true_14: forall F, In F LF_14 -> forall u1: nat, forall u2: nat, forall u3: tree, forall u4: tree, fst (F u1  u2 u3  u4).
Proof.
let n := constr:(4) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_14);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_14;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_14: forall (u1: nat) (u2: tree), (flat (ins u1 u2)) = (Cons u1 (flat u2)).
Proof.
do 2 intro.
apply (all_true_14 F_14);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_82 :=  list ->  list ->  list ->  nat -> (Prop * (List.list term)).

Definition F_82 : type_LF_82:= (fun   u1 u2 u3  _ => ((app u1 (app u2 u3)) = (app (app u1 u2) u3), (Term id_app ((model_list u1):: (Term id_app ((model_list u2):: (model_list u3)::nil))::nil))::(Term id_app ((Term id_app ((model_list u1):: (model_list u2)::nil)):: (model_list u3)::nil))::nil)).
Definition F_93 : type_LF_82:= (fun   u2 u3 _  _ => ((app u2 u3) = (app (app Nil u2) u3), (Term id_app ((model_list u2):: (model_list u3)::nil))::(Term id_app ((Term id_app ((Term id_Nil nil):: (model_list u2)::nil)):: (model_list u3)::nil))::nil)).
Definition F_108 : type_LF_82:= (fun   u2 u3 _  _ => ((app u2 u3) = (app u2 u3), (Term id_app ((model_list u2):: (model_list u3)::nil))::(Term id_app ((model_list u2):: (model_list u3)::nil))::nil)).
Definition F_99 : type_LF_82:= (fun   u2 u3 u5 u4 => ((Cons u4 (app u5 (app u2 u3))) = (app (app (Cons u4 u5) u2) u3), (Term id_Cons ((model_nat u4):: (Term id_app ((model_list u5):: (Term id_app ((model_list u2):: (model_list u3)::nil))::nil))::nil))::(Term id_app ((Term id_app ((Term id_Cons ((model_nat u4):: (model_list u5)::nil)):: (model_list u2)::nil)):: (model_list u3)::nil))::nil)).
Definition F_112 : type_LF_82:= (fun   u2 u3 u5 u4 => ((Cons u4 (app u5 (app u2 u3))) = (app (Cons u4 (app u5 u2)) u3), (Term id_Cons ((model_nat u4):: (Term id_app ((model_list u5):: (Term id_app ((model_list u2):: (model_list u3)::nil))::nil))::nil))::(Term id_app ((Term id_Cons ((model_nat u4):: (Term id_app ((model_list u5):: (model_list u2)::nil))::nil)):: (model_list u3)::nil))::nil)).
Definition F_117 : type_LF_82:= (fun   u2 u3 u5 u4 => ((Cons u4 (app u5 (app u2 u3))) = (Cons u4 (app (app u5 u2) u3)), (Term id_Cons ((model_nat u4):: (Term id_app ((model_list u5):: (Term id_app ((model_list u2):: (model_list u3)::nil))::nil))::nil))::(Term id_Cons ((model_nat u4):: (Term id_app ((Term id_app ((model_list u5):: (model_list u2)::nil)):: (model_list u3)::nil))::nil))::nil)).
Definition F_120 : type_LF_82:= (fun    _ _ _ u4 => (u4 = u4, (model_nat u4)::(model_nat u4)::nil)).

Definition LF_82 := [F_82, F_93, F_108, F_99, F_112, F_117, F_120].


Function f_82 (u1: list) (u2: list) (u3: list) {struct u1} : list :=
 match u1, u2, u3 with
| Nil, _, _ => Nil
| (Cons u4 u5), _, _ => Nil
end.

Lemma main_82 : forall F, In F LF_82 -> forall u1, forall u2, forall u3, forall u4, (forall F', In F' LF_82 -> forall e1, forall e2, forall e3, forall e4, less (snd (F' e1 e2 e3 e4)) (snd (F u1 u2 u3 u4)) -> fst (F' e1 e2 e3 e4)) -> fst (F u1 u2 u3 u4).
Proof.
intros F HF u1 u2 u3 u4; case_In HF; intro Hind.

	(* GENERATE on [ 82 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. 

revert Hind.

pattern u1, u2, u3, (f_82 u1 u2 u3). apply f_82_ind.

(* case [ 93 ] *)

intros _u1 _u2 _u3.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_93). clear HFabs0.
assert (HFabs0 : fst (F_93 _u2 _u3 Nil 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_93. unfold F_82. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_82. unfold F_93.
auto.


(* case [ 99 ] *)

intros _u1 _u2 _u3. intro u4. intro u5.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_99). clear HFabs0.
assert (HFabs0 : fst (F_99 _u2 _u3 u5 u4)).
apply Hind. trivial_in 3. unfold snd. unfold F_99. unfold F_82. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_82. unfold F_99.
auto.





	(* REWRITING on [ 93 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into d_u3. rename u4 into d_u4. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_108). clear Hind.
assert (HFabs1 : fst (F_108 u2 u3 Nil 0)).
apply Res. trivial_in 2. unfold snd. unfold F_108. unfold F_93. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_93. unfold fst in HFabs1. unfold F_108 in HFabs1.   
pattern u2. simpl (app _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 108 ] *)

unfold fst. unfold F_108.
auto.



	(* REWRITING on [ 99 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u5. rename u4 into _u4. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u4 into u4. 
assert (Res := Hind F_112). clear Hind.
assert (HFabs1 : fst (F_112 u2 u3 u5 u4)).
apply Res. trivial_in 4. unfold snd. unfold F_112. unfold F_99. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_99. unfold fst in HFabs1. unfold F_112 in HFabs1.   
pattern u4, u5, u2. simpl (app _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 112 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u5. rename u4 into _u4. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u4 into u4. 
assert (Res := Hind F_117). clear Hind.
assert (HFabs1 : fst (F_117 u2 u3 u5 u4)).
apply Res. trivial_in 5. unfold snd. unfold F_117. unfold F_112. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_112. unfold fst in HFabs1. unfold F_117 in HFabs1.   
pattern u4, (app u5 u2), u3. simpl (app _ _). cbv beta.
 simpl. auto.



	(* POSITIVE DECOMPOSITION on [ 117 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u5. rename u4 into _u4. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u4 into u4. 
assert (H2 := Hind F_120). 
assert (HFabs2 : fst (F_120 Nil Nil Nil u4)).
apply H2. trivial_in 6. unfold snd. unfold F_120. unfold F_117. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_117. unfold F_120.

unfold fst in HFabs2. unfold F_120 in HFabs2.



assert (H1 := Hind F_82). 
assert (HFabs1 : fst (F_82 u5 u2 u3 0)).
apply H1. trivial_in 0. unfold snd. unfold F_82. unfold F_117. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_117. unfold F_82.

unfold fst in HFabs1. unfold F_82 in HFabs1.

repeat (auto || (rewrite HFabs2|| rewrite HFabs1||  auto)).


	(* TAUTOLOGY on [ 120 ] *)

unfold fst. unfold F_120.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_82 := fun f => exists F, In F LF_82 /\ exists e1, exists e2, exists e3, exists e4, f = F e1 e2 e3 e4.

Theorem all_true_82: forall F, In F LF_82 -> forall u1: list, forall u2: list, forall u3: list, forall u4: nat, fst (F u1  u2  u3 u4).
Proof.
let n := constr:(4) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_82);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_82;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_82: forall (u1: list) (u2: list) (u3: list), (app u1 (app u2 u3)) = (app (app u1 u2) u3).
Proof.
do 3 intro.
apply (all_true_82 F_82);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
