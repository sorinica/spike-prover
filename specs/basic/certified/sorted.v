
Require Import sorted_spec.



Definition type_LF_41 :=  list ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_41 : type_LF_41:= (fun  u2 u1 _ => ((sorted (Cons u1 u2)) = true -> (sorted u2) = true, (Term id_sorted ((Term id_Cons ((model_nat u1):: (model_list u2)::nil))::nil))::(Term id_true nil)::(Term id_sorted ((model_list u2)::nil))::(Term id_true nil)::nil)).
Definition F_60 : type_LF_41:= (fun  u5 u1 u4 => ((sorted (Cons u4 u5)) = true -> (leq u1 u4) = true -> (sorted (Cons u4 u5)) = true, (Term id_sorted ((Term id_Cons ((model_nat u4):: (model_list u5)::nil))::nil))::(Term id_true nil)::(Term id_leq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sorted ((Term id_Cons ((model_nat u4):: (model_list u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_66 : type_LF_41:= (fun  u5 u1 u4 => (false = true -> (leq u1 u4) = false -> (sorted (Cons u4 u5)) = true, (Term id_false nil)::(Term id_true nil)::(Term id_leq ((model_nat u1):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_sorted ((Term id_Cons ((model_nat u4):: (model_list u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_54 : type_LF_41:= (fun   _  _ _ => (true = true -> (sorted Nil) = true, (Term id_true nil)::(Term id_true nil)::(Term id_sorted ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_68 : type_LF_41:= (fun   _  _ _ => ((sorted Nil) = true, (Term id_sorted ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_72 : type_LF_41:= (fun   _  _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).

Definition LF_41 := [F_41, F_60, F_66, F_54, F_68, F_72].


Function f_41 (u2: list) (u1: nat) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons u4 u5), _ => true
end.

Lemma main_41 : forall F, In F LF_41 -> forall u1, forall u2, forall u3, (forall F', In F' LF_41 -> forall e1, forall e2, forall e3, less (snd (F' e1 e2 e3)) (snd (F u1 u2 u3)) -> fst (F' e1 e2 e3)) -> fst (F u1 u2 u3).
Proof.
intros F HF u1 u2 u3; case_In HF; intro Hind.

	(* GENERATE on [ 41 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_41 u2 u1). apply f_41_ind.

(* case [ 54 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_54). clear HFabs0.
assert (HFabs0 : fst (F_54 Nil 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_54. unfold F_41. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_41. unfold F_54.
auto.



intros _u2 _u1. intro u4. intro u5.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
case_eq (leq _u1 u4); [intro H | intro H].

(* case [ 60 ] *)

assert (Hind := HFabs0 F_60). clear HFabs0.
assert (HFabs0 : fst (F_60 u5 _u1 u4)).
apply Hind. trivial_in 1. unfold snd. unfold F_60. unfold F_41. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_41. unfold F_60. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 66 ] *)

assert (Hind := HFabs0 F_66). clear HFabs0.
assert (HFabs0 : fst (F_66 u5 _u1 u4)).
apply Hind. trivial_in 2. unfold snd. unfold F_66. unfold F_41. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_41. unfold F_66. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* TAUTOLOGY on [ 60 ] *)

unfold fst. unfold F_60.
auto.



	(* NEGATIVE CLASH on [ 66 ] *)

unfold fst. unfold F_66. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 54 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. 

assert (H := Hind F_68). 
assert (HFabs0 : fst (F_68 Nil 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_68. unfold F_54. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_54. unfold F_68.

unfold fst in HFabs0. unfold F_68 in HFabs0.
auto.



	(* REWRITING on [ 68 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. 

assert (Res := Hind F_72). clear Hind.
assert (HFabs1 : fst (F_72 Nil 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_72. unfold F_68. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_68. unfold fst in HFabs1. unfold F_72 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 72 ] *)

unfold fst. unfold F_72.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_41 := fun f => exists F, In F LF_41 /\ exists e1, exists e2, exists e3, f = F e1 e2 e3.

Theorem all_true_41: forall F, In F LF_41 -> forall u1: list, forall u2: nat, forall u3: nat, fst (F u1 u2  u3).
Proof.
let n := constr:(3) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_41);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_41;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_41: forall (u2: list) (u1: nat), (sorted (Cons u1 u2)) = true -> (sorted u2) = true.
Proof.
do 2 intro.
apply (all_true_41 F_41);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_73 :=  list ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_73 : type_LF_73:= (fun  u2 u1 _ => ((length (insert u1 u2)) = (S (length u2)), (Term id_length ((Term id_insert ((model_nat u1):: (model_list u2)::nil))::nil))::(Term id_S ((Term id_length ((model_list u2)::nil))::nil))::nil)).
Definition F_86 : type_LF_73:= (fun   _ u1 _ => ((length (Cons u1 Nil)) = (S (length Nil)), (Term id_length ((Term id_Cons ((model_nat u1):: (Term id_Nil nil)::nil))::nil))::(Term id_S ((Term id_length ((Term id_Nil nil)::nil))::nil))::nil)).
Definition F_111 : type_LF_73:= (fun   _  _ _ => ((S (length Nil)) = (S (length Nil)), (Term id_S ((Term id_length ((Term id_Nil nil)::nil))::nil))::(Term id_S ((Term id_length ((Term id_Nil nil)::nil))::nil))::nil)).
Definition F_92 : type_LF_73:= (fun  u5 u1 u4 => ((leq u1 u4) = true -> (length (Cons u1 (Cons u4 u5))) = (S (length (Cons u4 u5))), (Term id_leq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_length ((Term id_Cons ((model_nat u1):: (Term id_Cons ((model_nat u4):: (model_list u5)::nil))::nil))::nil))::(Term id_S ((Term id_length ((Term id_Cons ((model_nat u4):: (model_list u5)::nil))::nil))::nil))::nil)).
Definition F_114 : type_LF_73:= (fun  u5 u1 u4 => ((leq u1 u4) = true -> (S (length (Cons u4 u5))) = (S (length (Cons u4 u5))), (Term id_leq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_S ((Term id_length ((Term id_Cons ((model_nat u4):: (model_list u5)::nil))::nil))::nil))::(Term id_S ((Term id_length ((Term id_Cons ((model_nat u4):: (model_list u5)::nil))::nil))::nil))::nil)).
Definition F_98 : type_LF_73:= (fun  u5 u1 u4 => ((leq u1 u4) = false -> (length (Cons u4 (insert u1 u5))) = (S (length (Cons u4 u5))), (Term id_leq ((model_nat u1):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_length ((Term id_Cons ((model_nat u4):: (Term id_insert ((model_nat u1):: (model_list u5)::nil))::nil))::nil))::(Term id_S ((Term id_length ((Term id_Cons ((model_nat u4):: (model_list u5)::nil))::nil))::nil))::nil)).
Definition F_117 : type_LF_73:= (fun  u5 u1 u4 => ((leq u1 u4) = false -> (S (length (insert u1 u5))) = (S (length (Cons u4 u5))), (Term id_leq ((model_nat u1):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_S ((Term id_length ((Term id_insert ((model_nat u1):: (model_list u5)::nil))::nil))::nil))::(Term id_S ((Term id_length ((Term id_Cons ((model_nat u4):: (model_list u5)::nil))::nil))::nil))::nil)).
Definition F_120 : type_LF_73:= (fun  u5 u1 u4 => ((leq u1 u4) = false -> (length (insert u1 u5)) = (length (Cons u4 u5)), (Term id_leq ((model_nat u1):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_length ((Term id_insert ((model_nat u1):: (model_list u5)::nil))::nil))::(Term id_length ((Term id_Cons ((model_nat u4):: (model_list u5)::nil))::nil))::nil)).
Definition F_126 : type_LF_73:= (fun  u5 u1 u4 => ((leq u1 u4) = false -> (S (length u5)) = (length (Cons u4 u5)), (Term id_leq ((model_nat u1):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_S ((Term id_length ((model_list u5)::nil))::nil))::(Term id_length ((Term id_Cons ((model_nat u4):: (model_list u5)::nil))::nil))::nil)).
Definition F_132 : type_LF_73:= (fun  u5 u1 u4 => ((leq u1 u4) = false -> (S (length u5)) = (S (length u5)), (Term id_leq ((model_nat u1):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_S ((Term id_length ((model_list u5)::nil))::nil))::(Term id_S ((Term id_length ((model_list u5)::nil))::nil))::nil)).

Definition LF_73 := [F_73, F_86, F_111, F_92, F_114, F_98, F_117, F_120, F_126, F_132].


Function f_73 (u2: list) (u1: nat) {struct u2} : list :=
 match u2, u1 with
| Nil, _ => Nil
| (Cons u4 u5), _ => Nil
end.

Lemma main_73 : forall F, In F LF_73 -> forall u1, forall u2, forall u3, (forall F', In F' LF_73 -> forall e1, forall e2, forall e3, less (snd (F' e1 e2 e3)) (snd (F u1 u2 u3)) -> fst (F' e1 e2 e3)) -> fst (F u1 u2 u3).
Proof.
intros F HF u1 u2 u3; case_In HF; intro Hind.

	(* GENERATE on [ 73 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_73 u2 u1). apply f_73_ind.

(* case [ 86 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_86). clear HFabs0.
assert (HFabs0 : fst (F_86 Nil _u1 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_86. unfold F_73. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_73. unfold F_86.
auto.



intros _u2 _u1. intro u4. intro u5.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
case_eq (leq _u1 u4); [intro H | intro H].

(* case [ 92 ] *)

assert (Hind := HFabs0 F_92). clear HFabs0.
assert (HFabs0 : fst (F_92 u5 _u1 u4)).
apply Hind. trivial_in 3. unfold snd. unfold F_92. unfold F_73. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_73. unfold F_92. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 98 ] *)

assert (Hind := HFabs0 F_98). clear HFabs0.
assert (HFabs0 : fst (F_98 u5 _u1 u4)).
apply Hind. trivial_in 5. unfold snd. unfold F_98. unfold F_73. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_73. unfold F_98. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* REWRITING on [ 86 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. 
rename _u1 into u1. 
assert (Res := Hind F_111). clear Hind.
assert (HFabs1 : fst (F_111 Nil 0 0)).
apply Res. trivial_in 2. unfold snd. unfold F_111. unfold F_86. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_86. unfold fst in HFabs1. unfold F_111 in HFabs1.   
pattern u1, Nil. simpl (length _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 111 ] *)

unfold fst. unfold F_111.
auto.



	(* REWRITING on [ 92 ] *)

rename u1 into _u5. rename u2 into _u1. rename u3 into _u4. 
rename _u5 into u5. rename _u1 into u1. rename _u4 into u4. 
assert (Res := Hind F_114). clear Hind.
assert (HFabs1 : fst (F_114 u5 u1 u4)).
apply Res. trivial_in 4. unfold snd. unfold F_114. unfold F_92. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_92. unfold fst in HFabs1. unfold F_114 in HFabs1.   
pattern u1, (Cons u4 u5). simpl (length _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 114 ] *)

unfold fst. unfold F_114.
auto.



	(* REWRITING on [ 98 ] *)

rename u1 into _u5. rename u2 into _u1. rename u3 into _u4. 
rename _u5 into u5. rename _u1 into u1. rename _u4 into u4. 
assert (Res := Hind F_117). clear Hind.
assert (HFabs1 : fst (F_117 u5 u1 u4)).
apply Res. trivial_in 6. unfold snd. unfold F_117. unfold F_98. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_98. unfold fst in HFabs1. unfold F_117 in HFabs1.   
pattern u4, (insert u1 u5). simpl (length _). cbv beta.
 simpl. auto.



	(* POSITIVE DECOMPOSITION on [ 117 ] *)

rename u1 into _u5. rename u2 into _u1. rename u3 into _u4. 
rename _u5 into u5. rename _u1 into u1. rename _u4 into u4. 
assert (H1 := Hind F_120). 
assert (HFabs1 : fst (F_120 u5 u1 u4)).
apply H1. trivial_in 7. unfold snd. unfold F_120. unfold F_117. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_117. unfold F_120.

unfold fst in HFabs1. unfold F_120 in HFabs1.

repeat (auto || (rewrite HFabs1||  auto)).


	(* REWRITING on [ 120 ] *)

rename u1 into _u5. rename u2 into _u1. rename u3 into _u4. 
rename _u5 into u5. rename _u1 into u1. rename _u4 into u4. 
assert (H := Hind F_73).
assert (Res := Hind F_126). clear Hind.
assert (HFabs0 : fst (F_73 u5 u1 0)).
apply H. trivial_in 0. unfold snd. unfold F_73. unfold F_120. rewrite_model. abstract solve_rpo_mul.
unfold fst in HFabs0. unfold F_73 in HFabs0. simpl in HFabs0.

assert (HFabs1 : fst (F_126 u5 u1 u4)).
apply Res. trivial_in 8. unfold snd. unfold F_126. unfold F_120. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_120. unfold fst in HFabs1. unfold F_126 in HFabs1.   
pattern u1, u5. simpl (length _). cbv beta.
try rewrite  HFabs0.  simpl. auto.



	(* REWRITING on [ 126 ] *)

rename u1 into _u5. rename u2 into _u1. rename u3 into _u4. 
rename _u5 into u5. rename _u1 into u1. rename _u4 into u4. 
assert (Res := Hind F_132). clear Hind.
assert (HFabs1 : fst (F_132 u5 u1 u4)).
apply Res. trivial_in 9. unfold snd. unfold F_132. unfold F_126. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_126. unfold fst in HFabs1. unfold F_132 in HFabs1.   
pattern u4, u5. simpl (length _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 132 ] *)

unfold fst. unfold F_132.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_73 := fun f => exists F, In F LF_73 /\ exists e1, exists e2, exists e3, f = F e1 e2 e3.

Theorem all_true_73: forall F, In F LF_73 -> forall u1: list, forall u2: nat, forall u3: nat, fst (F u1 u2  u3).
Proof.
let n := constr:(3) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_73);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_73;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_73: forall (u2: list) (u1: nat), (length (insert u1 u2)) = (S (length u2)).
Proof.
do 2 intro.
apply (all_true_73 F_73);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_134 :=  list ->  nat -> (Prop * (List.list term)).

Definition F_134 : type_LF_134:= (fun  u1  _ => ((length (isort u1)) = (length u1), (Term id_length ((Term id_isort ((model_list u1)::nil))::nil))::(Term id_length ((model_list u1)::nil))::nil)).
Definition F_146 : type_LF_134:= (fun   _  _ => ((length Nil) = (length Nil), (Term id_length ((Term id_Nil nil)::nil))::(Term id_length ((Term id_Nil nil)::nil))::nil)).
Definition F_152 : type_LF_134:= (fun  u3 u2 => ((length (insert u2 (isort u3))) = (length (Cons u2 u3)), (Term id_length ((Term id_insert ((model_nat u2):: (Term id_isort ((model_list u3)::nil))::nil))::nil))::(Term id_length ((Term id_Cons ((model_nat u2):: (model_list u3)::nil))::nil))::nil)).
Definition F_158 : type_LF_134:= (fun  u3 u2 => ((S (length (isort u3))) = (length (Cons u2 u3)), (Term id_S ((Term id_length ((Term id_isort ((model_list u3)::nil))::nil))::nil))::(Term id_length ((Term id_Cons ((model_nat u2):: (model_list u3)::nil))::nil))::nil)).
Definition F_165 : type_LF_134:= (fun  u3 u2 => ((S (length u3)) = (length (Cons u2 u3)), (Term id_S ((Term id_length ((model_list u3)::nil))::nil))::(Term id_length ((Term id_Cons ((model_nat u2):: (model_list u3)::nil))::nil))::nil)).
Definition F_173 : type_LF_134:= (fun  u3  _ => ((S (length u3)) = (S (length u3)), (Term id_S ((Term id_length ((model_list u3)::nil))::nil))::(Term id_S ((Term id_length ((model_list u3)::nil))::nil))::nil)).

Definition LF_134 := [F_134, F_146, F_152, F_158, F_165, F_173].


Function f_134 (u1: list) {struct u1} : list :=
 match u1 with
| Nil => Nil
| (Cons u2 u3) => Nil
end.

Lemma main_134 : forall F, In F LF_134 -> forall u1, forall u2, (forall F', In F' LF_134 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 134 ] *)

rename u1 into _u1. rename u2 into d_u2. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_134 u1). apply f_134_ind.

(* case [ 146 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_146). clear HFabs0.
assert (HFabs0 : fst (F_146 Nil 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_146. unfold F_134. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_134. unfold F_146.
auto.


(* case [ 152 ] *)

intros _u1. intro u2. intro u3.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_152). clear HFabs0.
assert (HFabs0 : fst (F_152 u3 u2)).
apply Hind. trivial_in 2. unfold snd. unfold F_152. unfold F_134. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_134. unfold F_152.
auto.





	(* TAUTOLOGY on [ 146 ] *)

unfold fst. unfold F_146.
auto.



	(* REWRITING on [ 152 ] *)

rename u1 into _u3. rename u2 into _u2. 
rename _u3 into u3. rename _u2 into u2. 
assert (Res := Hind F_158). clear Hind.
assert (HFabs1 : fst (F_158 u3 u2)).
apply Res. trivial_in 3. unfold snd. unfold F_158. unfold F_152. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_152. unfold fst in HFabs1. unfold F_158 in HFabs1.  specialize true_73 with (u1 := u2) (u2 := (isort u3)). intro L. try rewrite L.
  simpl. auto.



	(* REWRITING on [ 158 ] *)

rename u1 into _u3. rename u2 into _u2. 
rename _u3 into u3. rename _u2 into u2. 
assert (H := Hind F_134).
assert (Res := Hind F_165). clear Hind.
assert (HFabs0 : fst (F_134 u3 0)).
apply H. trivial_in 0. unfold snd. unfold F_134. unfold F_158. rewrite_model. abstract solve_rpo_mul.
unfold fst in HFabs0. unfold F_134 in HFabs0. simpl in HFabs0.

assert (HFabs1 : fst (F_165 u3 u2)).
apply Res. trivial_in 4. unfold snd. unfold F_165. unfold F_158. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_158. unfold fst in HFabs1. unfold F_165 in HFabs1.   
pattern u3. simpl (length _). cbv beta.
try rewrite  HFabs0.  simpl. auto.



	(* REWRITING on [ 165 ] *)

rename u1 into _u3. rename u2 into _u2. 
rename _u3 into u3. rename _u2 into u2. 
assert (Res := Hind F_173). clear Hind.
assert (HFabs1 : fst (F_173 u3 0)).
apply Res. trivial_in 5. unfold snd. unfold F_173. unfold F_165. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_165. unfold fst in HFabs1. unfold F_173 in HFabs1.   
pattern u2, u3. simpl (length _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 173 ] *)

unfold fst. unfold F_173.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_134 := fun f => exists F, In F LF_134 /\ exists e1, exists e2, f = F e1 e2.

Theorem all_true_134: forall F, In F LF_134 -> forall u1: list, forall u2: nat, fst (F u1 u2).
Proof.
let n := constr:(2) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_134);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_134;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_134: forall (u1: list), (length (isort u1)) = (length u1).
Proof.
do 1 intro.
apply (all_true_134 F_134);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_175 :=  list ->  nat -> (Prop * (List.list term)).

Definition F_175 : type_LF_175:= (fun  u1  _ => ((sorted (isort u1)) = true, (Term id_sorted ((Term id_isort ((model_list u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_189 : type_LF_175:= (fun   _  _ => ((sorted Nil) = true, (Term id_sorted ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_208 : type_LF_175:= (fun   _  _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).
Definition F_195 : type_LF_175:= (fun  u3 u2 => ((sorted (insert u2 (isort u3))) = true, (Term id_sorted ((Term id_insert ((model_nat u2):: (Term id_isort ((model_list u3)::nil))::nil))::nil))::(Term id_true nil)::nil)).

Definition LF_175 := [F_175, F_189, F_208, F_195].


Function f_175 (u1: list) {struct u1} : list :=
 match u1 with
| Nil => Nil
| (Cons u2 u3) => Nil
end.


Hypothesis true_39: forall u1 u2, (sorted (insert u1 u2)) = (sorted u2).

Lemma main_175 : forall F, In F LF_175 -> forall u1, forall u2, (forall F', In F' LF_175 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 175 ] *)

rename u1 into _u1. rename u2 into d_u2. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_175 u1). apply f_175_ind.

(* case [ 189 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_189). clear HFabs0.
assert (HFabs0 : fst (F_189 Nil 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_189. unfold F_175. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_175. unfold F_189.
auto.


(* case [ 195 ] *)

intros _u1. intro u2. intro u3.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_195). clear HFabs0.
assert (HFabs0 : fst (F_195 u3 u2)).
apply Hind. trivial_in 3. unfold snd. unfold F_195. unfold F_175. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_175. unfold F_195.
auto.





	(* REWRITING on [ 189 ] *)

rename u1 into d_u1. rename u2 into d_u2. 

assert (Res := Hind F_208). clear Hind.
assert (HFabs1 : fst (F_208 Nil 0)).
apply Res. trivial_in 2. unfold snd. unfold F_208. unfold F_189. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_189. unfold fst in HFabs1. unfold F_208 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 208 ] *)

unfold fst. unfold F_208.
auto.



	(* REWRITING on [ 195 ] *)

rename u1 into _u3. rename u2 into _u2. 
rename _u3 into u3. rename _u2 into u2. 
assert (Res := Hind F_175). clear Hind.
assert (HFabs1 : fst (F_175 u3 0)).
apply Res. trivial_in 0. unfold snd. unfold F_175. unfold F_195. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_195. unfold fst in HFabs1. unfold F_175 in HFabs1.  specialize true_39 with (u1 := u2) (u2 := (isort u3)). intro L. try rewrite L.
  simpl. auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_175 := fun f => exists F, In F LF_175 /\ exists e1, exists e2, f = F e1 e2.

Theorem all_true_175: forall F, In F LF_175 -> forall u1: list, forall u2: nat, fst (F u1 u2).
Proof.
let n := constr:(2) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_175);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_175;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_175: forall (u1: list), (sorted (isort u1)) = true.
Proof.
do 1 intro.
apply (all_true_175 F_175);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
