
Require Import even_odd_spec.



Definition type_LF_46 :=  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_46 : type_LF_46:= (fun  u1 u2 u3 => ((evenr (plus u1 u2)) = true -> (evenr (plus u2 u3)) = true -> (evenr (plus u1 u3)) = true, (Term id_evenr ((Term id_plus ((model_nat u1):: (model_nat u2)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u1):: (model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_56 : type_LF_46:= (fun  u2 u3 _ => ((evenr (plus 0 u2)) = true -> (evenr (plus u2 u3)) = true -> (evenr u3) = true, (Term id_evenr ((Term id_plus ((Term id_0 nil):: (model_nat u2)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((model_nat u3)::nil))::(Term id_true nil)::nil)).
Definition F_62 : type_LF_46:= (fun  u2 u3 u4 => ((evenr (plus (S u4) u2)) = true -> (evenr (plus u2 u3)) = true -> (evenr (S (plus u4 u3))) = true, (Term id_evenr ((Term id_plus ((Term id_S ((model_nat u4)::nil)):: (model_nat u2)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((Term id_plus ((model_nat u4):: (model_nat u3)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_69 : type_LF_46:= (fun  u2 u3 _ => ((evenr u2) = true -> (evenr (plus u2 u3)) = true -> (evenr u3) = true, (Term id_evenr ((model_nat u2)::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((model_nat u3)::nil))::(Term id_true nil)::nil)).
Definition F_88 : type_LF_46:= (fun  u3 _ _ => ((evenr 0) = true -> (evenr u3) = true -> (evenr u3) = true, (Term id_evenr ((Term id_0 nil)::nil))::(Term id_true nil)::(Term id_evenr ((model_nat u3)::nil))::(Term id_true nil)::(Term id_evenr ((model_nat u3)::nil))::(Term id_true nil)::nil)).
Definition F_94 : type_LF_46:= (fun  u3 u4 _ => ((evenr (S u4)) = true -> (evenr (S (plus u4 u3))) = true -> (evenr u3) = true, (Term id_evenr ((Term id_S ((model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((Term id_plus ((model_nat u4):: (model_nat u3)::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((model_nat u3)::nil))::(Term id_true nil)::nil)).
Definition F_112 : type_LF_46:= (fun  u3 _ _ => ((evenr (S 0)) = true -> (evenr (S u3)) = true -> (evenr u3) = true, (Term id_evenr ((Term id_S ((Term id_0 nil)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((model_nat u3)::nil))::(Term id_true nil)::nil)).
Definition F_127 : type_LF_46:= (fun  u3 _ _ => (false = true -> (evenr (S u3)) = true -> (evenr u3) = true, (Term id_false nil)::(Term id_true nil)::(Term id_evenr ((Term id_S ((model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((model_nat u3)::nil))::(Term id_true nil)::nil)).
Definition F_118 : type_LF_46:= (fun  u3 u5 _ => ((evenr (S (S u5))) = true -> (evenr (S (S (plus u5 u3)))) = true -> (evenr u3) = true, (Term id_evenr ((Term id_S ((Term id_S ((model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((Term id_S ((Term id_plus ((model_nat u5):: (model_nat u3)::nil))::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((model_nat u3)::nil))::(Term id_true nil)::nil)).
Definition F_130 : type_LF_46:= (fun  u3 u5 _ => ((evenr (S (S u5))) = true -> (evenr (plus u5 u3)) = true -> (evenr u3) = true, (Term id_evenr ((Term id_S ((Term id_S ((model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u5):: (model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((model_nat u3)::nil))::(Term id_true nil)::nil)).
Definition F_72 : type_LF_46:= (fun  u2 u3 u4 => ((evenr (S (plus u4 u2))) = true -> (evenr (plus u2 u3)) = true -> (evenr (S (plus u4 u3))) = true, (Term id_evenr ((Term id_S ((Term id_plus ((model_nat u4):: (model_nat u2)::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((Term id_plus ((model_nat u4):: (model_nat u3)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_154 : type_LF_46:= (fun  u2 u3 _ => ((evenr (S (plus 0 u2))) = true -> (evenr (plus u2 u3)) = true -> (evenr (S u3)) = true, (Term id_evenr ((Term id_S ((Term id_plus ((Term id_0 nil):: (model_nat u2)::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_160 : type_LF_46:= (fun  u2 u3 u5 => ((evenr (S (plus (S u5) u2))) = true -> (evenr (plus u2 u3)) = true -> (evenr (S (S (plus u5 u3)))) = true, (Term id_evenr ((Term id_S ((Term id_plus ((Term id_S ((model_nat u5)::nil)):: (model_nat u2)::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((Term id_S ((Term id_plus ((model_nat u5):: (model_nat u3)::nil))::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_180 : type_LF_46:= (fun  u2 u3 u5 => ((evenr (S (plus (S u5) u2))) = true -> (evenr (plus u2 u3)) = true -> (evenr (plus u5 u3)) = true, (Term id_evenr ((Term id_S ((Term id_plus ((Term id_S ((model_nat u5)::nil)):: (model_nat u2)::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u5):: (model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_189 : type_LF_46:= (fun  u2 u3 u5 => ((evenr (S (S (plus u5 u2)))) = true -> (evenr (plus u2 u3)) = true -> (evenr (plus u5 u3)) = true, (Term id_evenr ((Term id_S ((Term id_S ((Term id_plus ((model_nat u5):: (model_nat u2)::nil))::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u5):: (model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_175 : type_LF_46:= (fun  u2 u3 _ => ((evenr (S u2)) = true -> (evenr (plus u2 u3)) = true -> (evenr (S u3)) = true, (Term id_evenr ((Term id_S ((model_nat u2)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_215 : type_LF_46:= (fun  u3 _ _ => ((evenr (S 0)) = true -> (evenr u3) = true -> (evenr (S u3)) = true, (Term id_evenr ((Term id_S ((Term id_0 nil)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((model_nat u3)::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_232 : type_LF_46:= (fun  u3 _ _ => (false = true -> (evenr u3) = true -> (evenr (S u3)) = true, (Term id_false nil)::(Term id_true nil)::(Term id_evenr ((model_nat u3)::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_221 : type_LF_46:= (fun  u3 u5 _ => ((evenr (S (S u5))) = true -> (evenr (S (plus u5 u3))) = true -> (evenr (S u3)) = true, (Term id_evenr ((Term id_S ((Term id_S ((model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((Term id_plus ((model_nat u5):: (model_nat u3)::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_235 : type_LF_46:= (fun  u3 u5 _ => ((evenr u5) = true -> (evenr (S (plus u5 u3))) = true -> (evenr (S u3)) = true, (Term id_evenr ((model_nat u5)::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((Term id_plus ((model_nat u5):: (model_nat u3)::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_258 : type_LF_46:= (fun  u3 _ _ => ((evenr 0) = true -> (evenr (S u3)) = true -> (evenr (S u3)) = true, (Term id_evenr ((Term id_0 nil)::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((model_nat u3)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_264 : type_LF_46:= (fun  u3 u6 _ => ((evenr (S u6)) = true -> (evenr (S (S (plus u6 u3)))) = true -> (evenr (S u3)) = true, (Term id_evenr ((Term id_S ((model_nat u6)::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((Term id_S ((Term id_plus ((model_nat u6):: (model_nat u3)::nil))::nil))::nil))::nil))::(Term id_true nil)::(Term id_evenr ((Term id_S ((model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).

Definition LF_46 := [F_46, F_56, F_62, F_69, F_88, F_94, F_112, F_127, F_118, F_130, F_72, F_154, F_160, F_180, F_189, F_175, F_215, F_232, F_221, F_235, F_258, F_264].


Function f_46 (u1: nat) (u3: nat) {struct u1} : nat :=
 match u1, u3 with
| 0, _ => 0
| (S u4), _ => 0
end.

Function f_69 (u2: nat) (u3: nat) {struct u2} : nat :=
 match u2, u3 with
| 0, _ => 0
| (S u4), _ => 0
end.

Function f_94 (u4: nat) (u3: nat) {struct u4} : nat :=
 match u4, u3 with
| 0, _ => 0
| (S u5), _ => 0
end.

Function f_72 (u4: nat) (u3: nat) {struct u4} : nat :=
 match u4, u3 with
| 0, _ => 0
| (S u5), _ => 0
end.

Function f_175 (u2: nat) (u3: nat) {struct u2} : nat :=
 match u2, u3 with
| 0, _ => 0
| (S u5), _ => 0
end.

Function f_235 (u5: nat) (u3: nat) {struct u5} : nat :=
 match u5, u3 with
| 0, _ => 0
| (S u6), _ => 0
end.

Lemma main_46 : forall F, In F LF_46 -> forall u1, forall u2, forall u3, (forall F', In F' LF_46 -> forall e1, forall e2, forall e3, less (snd (F' e1 e2 e3)) (snd (F u1 u2 u3)) -> fst (F' e1 e2 e3)) -> fst (F u1 u2 u3).
Proof.
intros F HF u1 u2 u3; case_In HF; intro Hind.

	(* GENERATE on [ 46 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. 

revert Hind.

pattern u1, u3, (f_46 u1 u3). apply f_46_ind.

(* case [ 56 ] *)

intros _u1 _u3.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_56). clear HFabs0.
assert (HFabs0 : fst (F_56 u2 _u3 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_56. unfold F_46. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_46. unfold F_56.
auto.


(* case [ 62 ] *)

intros _u1 _u3. intro u4.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_62). clear HFabs0.
assert (HFabs0 : fst (F_62 u2 _u3 u4)).
apply Hind. trivial_in 2. unfold snd. unfold F_62. unfold F_46. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_46. unfold F_62.
auto.





	(* REWRITING on [ 56 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into d_u3. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_69). clear Hind.
assert (HFabs1 : fst (F_69 u2 u3 0)).
apply Res. trivial_in 3. unfold snd. unfold F_69. unfold F_56. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_56. unfold fst in HFabs1. unfold F_69 in HFabs1.   
pattern u2. simpl (plus _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 62 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_72). clear Hind.
assert (HFabs1 : fst (F_72 u2 u3 u4)).
apply Res. trivial_in 10. unfold snd. unfold F_72. unfold F_62. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_62. unfold fst in HFabs1. unfold F_72 in HFabs1.   
pattern u4, u2. simpl (plus _ _). cbv beta.
 simpl. auto.



	(* GENERATE on [ 69 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into d_u3. 
rename _u2 into u2. rename _u3 into u3. 

revert Hind.

pattern u2, u3, (f_69 u2 u3). apply f_69_ind.

(* case [ 88 ] *)

intros _u2 _u3.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_88). clear HFabs0.
assert (HFabs0 : fst (F_88 _u3 0 0)).
apply Hind. trivial_in 4. unfold snd. unfold F_88. unfold F_69. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_69. unfold F_88.
auto.


(* case [ 94 ] *)

intros _u2 _u3. intro u4.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_94). clear HFabs0.
assert (HFabs0 : fst (F_94 _u3 u4 0)).
apply Hind. trivial_in 5. unfold snd. unfold F_94. unfold F_69. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_69. unfold F_94.
auto.





	(* TAUTOLOGY on [ 88 ] *)

unfold fst. unfold F_88.
auto.



	(* GENERATE on [ 94 ] *)

rename u1 into _u3. rename u2 into _u4. rename u3 into d_u3. 
rename _u3 into u3. rename _u4 into u4. 

revert Hind.

pattern u4, u3, (f_94 u4 u3). apply f_94_ind.

(* case [ 112 ] *)

intros _u4 _u3.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_112). clear HFabs0.
assert (HFabs0 : fst (F_112 _u3 0 0)).
apply Hind. trivial_in 6. unfold snd. unfold F_112. unfold F_94. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_94. unfold F_112.
auto.


(* case [ 118 ] *)

intros _u4 _u3. intro u5.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_118). clear HFabs0.
assert (HFabs0 : fst (F_118 _u3 u5 0)).
apply Hind. trivial_in 8. unfold snd. unfold F_118. unfold F_94. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_94. unfold F_118.
auto.





	(* REWRITING on [ 112 ] *)

rename u1 into _u3. rename u2 into d_u2. rename u3 into d_u3. 
rename _u3 into u3. 
assert (Res := Hind F_127). clear Hind.
assert (HFabs1 : fst (F_127 u3 0 0)).
apply Res. trivial_in 7. unfold snd. unfold F_127. unfold F_112. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_112. unfold fst in HFabs1. unfold F_127 in HFabs1.    simpl. auto.



	(* NEGATIVE CLASH on [ 127 ] *)

unfold fst. unfold F_127. intros. try discriminate.



	(* REWRITING on [ 118 ] *)

rename u1 into _u3. rename u2 into _u5. rename u3 into d_u3. 
rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_130). clear Hind.
assert (HFabs1 : fst (F_130 u3 u5 0)).
apply Res. trivial_in 9. unfold snd. unfold F_130. unfold F_118. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_118. unfold fst in HFabs1. unfold F_130 in HFabs1.   
pattern (plus u5 u3). simpl (evenr _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 130 ] *)

rename u1 into _u3. rename u2 into _u5. rename u3 into d_u3. 
rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_69). clear Hind.
assert (HFabs1 : fst (F_69 u5 u3 0)).
apply Res. trivial_in 3. unfold snd. unfold F_69. unfold F_130. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_130. unfold fst in HFabs1. unfold F_69 in HFabs1.   
pattern u5. simpl (evenr _). cbv beta.
 simpl. auto.



	(* GENERATE on [ 72 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 

revert Hind.

pattern u4, u3, (f_72 u4 u3). apply f_72_ind.

(* case [ 154 ] *)

intros _u4 _u3.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_154). clear HFabs0.
assert (HFabs0 : fst (F_154 u2 _u3 0)).
apply Hind. trivial_in 11. unfold snd. unfold F_154. unfold F_72. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_72. unfold F_154.
auto.


(* case [ 160 ] *)

intros _u4 _u3. intro u5.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_160). clear HFabs0.
assert (HFabs0 : fst (F_160 u2 _u3 u5)).
apply Hind. trivial_in 12. unfold snd. unfold F_160. unfold F_72. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_72. unfold F_160.
auto.





	(* REWRITING on [ 154 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into d_u3. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_175). clear Hind.
assert (HFabs1 : fst (F_175 u2 u3 0)).
apply Res. trivial_in 15. unfold snd. unfold F_175. unfold F_154. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_154. unfold fst in HFabs1. unfold F_175 in HFabs1.   
pattern u2. simpl (plus _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 160 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u5. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_180). clear Hind.
assert (HFabs1 : fst (F_180 u2 u3 u5)).
apply Res. trivial_in 13. unfold snd. unfold F_180. unfold F_160. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_160. unfold fst in HFabs1. unfold F_180 in HFabs1.   
pattern (plus u5 u3). simpl (evenr _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 180 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u5. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_189). clear Hind.
assert (HFabs1 : fst (F_189 u2 u3 u5)).
apply Res. trivial_in 14. unfold snd. unfold F_189. unfold F_180. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_180. unfold fst in HFabs1. unfold F_189 in HFabs1.   
pattern u5, u2. simpl (plus _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 189 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u5. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_46). clear Hind.
assert (HFabs1 : fst (F_46 u5 u2 u3)).
apply Res. trivial_in 0. unfold snd. unfold F_46. unfold F_189. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_189. unfold fst in HFabs1. unfold F_46 in HFabs1.   
pattern (plus u5 u2). simpl (evenr _). cbv beta.
 simpl. auto.



	(* GENERATE on [ 175 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into d_u3. 
rename _u2 into u2. rename _u3 into u3. 

revert Hind.

pattern u2, u3, (f_175 u2 u3). apply f_175_ind.

(* case [ 215 ] *)

intros _u2 _u3.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_215). clear HFabs0.
assert (HFabs0 : fst (F_215 _u3 0 0)).
apply Hind. trivial_in 16. unfold snd. unfold F_215. unfold F_175. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_175. unfold F_215.
auto.


(* case [ 221 ] *)

intros _u2 _u3. intro u5.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_221). clear HFabs0.
assert (HFabs0 : fst (F_221 _u3 u5 0)).
apply Hind. trivial_in 18. unfold snd. unfold F_221. unfold F_175. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_175. unfold F_221.
auto.





	(* REWRITING on [ 215 ] *)

rename u1 into _u3. rename u2 into d_u2. rename u3 into d_u3. 
rename _u3 into u3. 
assert (Res := Hind F_232). clear Hind.
assert (HFabs1 : fst (F_232 u3 0 0)).
apply Res. trivial_in 17. unfold snd. unfold F_232. unfold F_215. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_215. unfold fst in HFabs1. unfold F_232 in HFabs1.    simpl. auto.



	(* NEGATIVE CLASH on [ 232 ] *)

unfold fst. unfold F_232. intros. try discriminate.



	(* REWRITING on [ 221 ] *)

rename u1 into _u3. rename u2 into _u5. rename u3 into d_u3. 
rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_235). clear Hind.
assert (HFabs1 : fst (F_235 u3 u5 0)).
apply Res. trivial_in 19. unfold snd. unfold F_235. unfold F_221. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_221. unfold fst in HFabs1. unfold F_235 in HFabs1.   
pattern u5. simpl (evenr _). cbv beta.
 simpl. auto.



	(* GENERATE on [ 235 ] *)

rename u1 into _u3. rename u2 into _u5. rename u3 into d_u3. 
rename _u3 into u3. rename _u5 into u5. 

revert Hind.

pattern u5, u3, (f_235 u5 u3). apply f_235_ind.

(* case [ 258 ] *)

intros _u5 _u3.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_258). clear HFabs0.
assert (HFabs0 : fst (F_258 _u3 0 0)).
apply Hind. trivial_in 20. unfold snd. unfold F_258. unfold F_235. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_235. unfold F_258.
auto.


(* case [ 264 ] *)

intros _u5 _u3. intro u6.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_264). clear HFabs0.
assert (HFabs0 : fst (F_264 _u3 u6 0)).
apply Hind. trivial_in 21. unfold snd. unfold F_264. unfold F_235. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_235. unfold F_264.
auto.





	(* TAUTOLOGY on [ 258 ] *)

unfold fst. unfold F_258.
auto.



	(* REWRITING on [ 264 ] *)

rename u1 into _u3. rename u2 into _u6. rename u3 into d_u3. 
rename _u3 into u3. rename _u6 into u6. 
assert (Res := Hind F_175). clear Hind.
assert (HFabs1 : fst (F_175 u6 u3 0)).
apply Res. trivial_in 15. unfold snd. unfold F_175. unfold F_264. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_264. unfold fst in HFabs1. unfold F_175 in HFabs1.   
pattern (plus u6 u3). simpl (evenr _). cbv beta.
 simpl. auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_46 := fun f => exists F, In F LF_46 /\ exists e1, exists e2, exists e3, f = F e1 e2 e3.

Theorem all_true_46: forall F, In F LF_46 -> forall u1: nat, forall u2: nat, forall u3: nat, fst (F u1  u2  u3).
Proof.
let n := constr:(3) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_46);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_46;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_46: forall (u1: nat) (u2: nat) (u3: nat), (evenr (plus u1 u2)) = true -> (evenr (plus u2 u3)) = true -> (evenr (plus u1 u3)) = true.
Proof.
do 3 intro.
apply (all_true_46 F_46);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_284 :=  nat -> (Prop * (List.list term)).

Definition F_284 : type_LF_284:= (fun  u1 => ((evenm u1) = (evenr u1), (Term id_evenm ((model_nat u1)::nil))::(Term id_evenr ((model_nat u1)::nil))::nil)).
Definition F_297 : type_LF_284:= (fun   _ => ((evenm 0) = true, (Term id_evenm ((Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_323 : type_LF_284:= (fun   _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).
Definition F_303 : type_LF_284:= (fun   _ => ((evenm (S 0)) = false, (Term id_evenm ((Term id_S ((Term id_0 nil)::nil))::nil))::(Term id_false nil)::nil)).
Definition F_309 : type_LF_284:= (fun  u2 => ((evenm (S (S u2))) = (evenr u2), (Term id_evenm ((Term id_S ((Term id_S ((model_nat u2)::nil))::nil))::nil))::(Term id_evenr ((model_nat u2)::nil))::nil)).
Definition F_326 : type_LF_284:= (fun   _ => ((oddm 0) = false, (Term id_oddm ((Term id_0 nil)::nil))::(Term id_false nil)::nil)).
Definition F_339 : type_LF_284:= (fun   _ => (false = false, (Term id_false nil)::(Term id_false nil)::nil)).
Definition F_333 : type_LF_284:= (fun  u2 => ((oddm (S u2)) = (evenr u2), (Term id_oddm ((Term id_S ((model_nat u2)::nil))::nil))::(Term id_evenr ((model_nat u2)::nil))::nil)).

Definition LF_284 := [F_284, F_297, F_323, F_303, F_309, F_326, F_339, F_333].


Function f_284 (u1: nat) {struct u1} : bool :=
 match u1 with
| 0 => true
| (S 0) => true
| (S (S u2)) => true
end.

Lemma main_284 : forall F, In F LF_284 -> forall u1, (forall F', In F' LF_284 -> forall e1, less (snd (F' e1)) (snd (F u1)) -> fst (F' e1)) -> fst (F u1).
Proof.
intros F HF u1; case_In HF; intro Hind.

	(* GENERATE on [ 284 ] *)

rename u1 into _u1. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_284 u1). apply f_284_ind.

(* case [ 297 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_297). clear HFabs0.
assert (HFabs0 : fst (F_297 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_297. unfold F_284. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_284. unfold F_297.
auto.


(* case [ 303 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_303). clear HFabs0.
assert (HFabs0 : fst (F_303 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_303. unfold F_284. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_284. unfold F_303.
auto.


(* case [ 309 ] *)

intros _u1. intro u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_309). clear HFabs0.
assert (HFabs0 : fst (F_309 u2)).
apply Hind. trivial_in 4. unfold snd. unfold F_309. unfold F_284. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_284. unfold F_309.
auto.





	(* REWRITING on [ 297 ] *)

rename u1 into d_u1. 

assert (Res := Hind F_323). clear Hind.
assert (HFabs1 : fst (F_323 0)).
apply Res. trivial_in 2. unfold snd. unfold F_323. unfold F_297. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_297. unfold fst in HFabs1. unfold F_323 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 323 ] *)

unfold fst. unfold F_323.
auto.



	(* REWRITING on [ 303 ] *)

rename u1 into d_u1. 

assert (Res := Hind F_326). clear Hind.
assert (HFabs1 : fst (F_326 0)).
apply Res. trivial_in 5. unfold snd. unfold F_326. unfold F_303. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_303. unfold fst in HFabs1. unfold F_326 in HFabs1.   
pattern 0. simpl (evenm _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 309 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_333). clear Hind.
assert (HFabs1 : fst (F_333 u2)).
apply Res. trivial_in 7. unfold snd. unfold F_333. unfold F_309. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_309. unfold fst in HFabs1. unfold F_333 in HFabs1.   
pattern (S u2). simpl (evenm _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 326 ] *)

rename u1 into d_u1. 

assert (Res := Hind F_339). clear Hind.
assert (HFabs1 : fst (F_339 0)).
apply Res. trivial_in 6. unfold snd. unfold F_339. unfold F_326. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_326. unfold fst in HFabs1. unfold F_339 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 339 ] *)

unfold fst. unfold F_339.
auto.



	(* REWRITING on [ 333 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_284). clear Hind.
assert (HFabs1 : fst (F_284 u2)).
apply Res. trivial_in 0. unfold snd. unfold F_284. unfold F_333. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_333. unfold fst in HFabs1. unfold F_284 in HFabs1.   
pattern u2. simpl (oddm _). cbv beta.
 simpl. auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_284 := fun f => exists F, In F LF_284 /\ exists e1, f = F e1.

Theorem all_true_284: forall F, In F LF_284 -> forall u1: nat, fst (F u1).
Proof.
let n := constr:(1) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_284);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_284;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_284: forall (u1: nat), (evenm u1) = (evenr u1).
Proof.
do 1 intro.
apply (all_true_284 F_284);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_347 :=  nat -> (Prop * (List.list term)).

Definition F_347 : type_LF_347:= (fun  u1 => ((plus u1 0) = u1, (Term id_plus ((model_nat u1):: (Term id_0 nil)::nil))::(model_nat u1)::nil)).
Definition F_359 : type_LF_347:= (fun   _ => (0 = 0, (Term id_0 nil)::(Term id_0 nil)::nil)).
Definition F_365 : type_LF_347:= (fun  u2 => ((S (plus u2 0)) = (S u2), (Term id_S ((Term id_plus ((model_nat u2):: (Term id_0 nil)::nil))::nil))::(Term id_S ((model_nat u2)::nil))::nil)).

Definition LF_347 := [F_347, F_359, F_365].


Function f_347 (u1: nat) {struct u1} : nat :=
 match u1 with
| 0 => 0
| (S u2) => 0
end.

Lemma main_347 : forall F, In F LF_347 -> forall u1, (forall F', In F' LF_347 -> forall e1, less (snd (F' e1)) (snd (F u1)) -> fst (F' e1)) -> fst (F u1).
Proof.
intros F HF u1; case_In HF; intro Hind.

	(* GENERATE on [ 347 ] *)

rename u1 into _u1. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_347 u1). apply f_347_ind.

(* case [ 359 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_359). clear HFabs0.
assert (HFabs0 : fst (F_359 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_359. unfold F_347. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_347. unfold F_359.
auto.


(* case [ 365 ] *)

intros _u1. intro u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_365). clear HFabs0.
assert (HFabs0 : fst (F_365 u2)).
apply Hind. trivial_in 2. unfold snd. unfold F_365. unfold F_347. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_347. unfold F_365.
auto.





	(* TAUTOLOGY on [ 359 ] *)

unfold fst. unfold F_359.
auto.



	(* POSITIVE DECOMPOSITION on [ 365 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (H1 := Hind F_347). 
assert (HFabs1 : fst (F_347 u2)).
apply H1. trivial_in 0. unfold snd. unfold F_347. unfold F_365. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_365. unfold F_347.

unfold fst in HFabs1. unfold F_347 in HFabs1.

repeat (auto || (rewrite HFabs1||  auto)).


Qed.



(* the set of all formula instances from the proof *)
Definition S_347 := fun f => exists F, In F LF_347 /\ exists e1, f = F e1.

Theorem all_true_347: forall F, In F LF_347 -> forall u1: nat, fst (F u1).
Proof.
let n := constr:(1) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_347);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_347;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_347: forall (u1: nat), (plus u1 0) = u1.
Proof.
do 1 intro.
apply (all_true_347 F_347);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_375 :=  nat ->  nat -> (Prop * (List.list term)).

Definition F_375 : type_LF_375:= (fun  u1 u2 => ((plus u1 (S u2)) = (S (plus u1 u2)), (Term id_plus ((model_nat u1):: (Term id_S ((model_nat u2)::nil))::nil))::(Term id_S ((Term id_plus ((model_nat u1):: (model_nat u2)::nil))::nil))::nil)).
Definition F_388 : type_LF_375:= (fun  u2 _ => ((S u2) = (S (plus 0 u2)), (Term id_S ((model_nat u2)::nil))::(Term id_S ((Term id_plus ((Term id_0 nil):: (model_nat u2)::nil))::nil))::nil)).
Definition F_394 : type_LF_375:= (fun  u2 u3 => ((S (plus u3 (S u2))) = (S (plus (S u3) u2)), (Term id_S ((Term id_plus ((model_nat u3):: (Term id_S ((model_nat u2)::nil))::nil))::nil))::(Term id_S ((Term id_plus ((Term id_S ((model_nat u3)::nil)):: (model_nat u2)::nil))::nil))::nil)).
Definition F_405 : type_LF_375:= (fun  u2 _ => (u2 = (plus 0 u2), (model_nat u2)::(Term id_plus ((Term id_0 nil):: (model_nat u2)::nil))::nil)).
Definition F_419 : type_LF_375:= (fun  u2 _ => (u2 = u2, (model_nat u2)::(model_nat u2)::nil)).
Definition F_411 : type_LF_375:= (fun  u2 u3 => ((plus u3 (S u2)) = (plus (S u3) u2), (Term id_plus ((model_nat u3):: (Term id_S ((model_nat u2)::nil))::nil))::(Term id_plus ((Term id_S ((model_nat u3)::nil)):: (model_nat u2)::nil))::nil)).
Definition F_423 : type_LF_375:= (fun  u2 u3 => ((S (plus u3 u2)) = (plus (S u3) u2), (Term id_S ((Term id_plus ((model_nat u3):: (model_nat u2)::nil))::nil))::(Term id_plus ((Term id_S ((model_nat u3)::nil)):: (model_nat u2)::nil))::nil)).
Definition F_431 : type_LF_375:= (fun  u2 u3 => ((S (plus u3 u2)) = (S (plus u3 u2)), (Term id_S ((Term id_plus ((model_nat u3):: (model_nat u2)::nil))::nil))::(Term id_S ((Term id_plus ((model_nat u3):: (model_nat u2)::nil))::nil))::nil)).

Definition LF_375 := [F_375, F_388, F_394, F_405, F_419, F_411, F_423, F_431].


Function f_375 (u1: nat) (u2: nat) {struct u1} : nat :=
 match u1, u2 with
| 0, _ => 0
| (S u3), _ => 0
end.

Lemma main_375 : forall F, In F LF_375 -> forall u1, forall u2, (forall F', In F' LF_375 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 375 ] *)

rename u1 into _u1. rename u2 into _u2. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_375 u1 u2). apply f_375_ind.

(* case [ 388 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_388). clear HFabs0.
assert (HFabs0 : fst (F_388 _u2 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_388. unfold F_375. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_375. unfold F_388.
auto.


(* case [ 394 ] *)

intros _u1 _u2. intro u3.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_394). clear HFabs0.
assert (HFabs0 : fst (F_394 _u2 u3)).
apply Hind. trivial_in 2. unfold snd. unfold F_394. unfold F_375. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_375. unfold F_394.
auto.





	(* POSITIVE DECOMPOSITION on [ 388 ] *)

rename u1 into _u2. rename u2 into d_u2. 
rename _u2 into u2. 
assert (H1 := Hind F_405). 
assert (HFabs1 : fst (F_405 u2 0)).
apply H1. trivial_in 3. unfold snd. unfold F_405. unfold F_388. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_388. unfold F_405.

unfold fst in HFabs1. unfold F_405 in HFabs1.

repeat (auto || (rewrite HFabs1||  auto)).


	(* POSITIVE DECOMPOSITION on [ 394 ] *)

rename u1 into _u2. rename u2 into _u3. 
rename _u2 into u2. rename _u3 into u3. 
assert (H1 := Hind F_411). 
assert (HFabs1 : fst (F_411 u2 u3)).
apply H1. trivial_in 5. unfold snd. unfold F_411. unfold F_394. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_394. unfold F_411.

unfold fst in HFabs1. unfold F_411 in HFabs1.

repeat (auto || (rewrite HFabs1||  auto)).


	(* REWRITING on [ 405 ] *)

rename u1 into _u2. rename u2 into d_u2. 
rename _u2 into u2. 
assert (Res := Hind F_419). clear Hind.
assert (HFabs1 : fst (F_419 u2 0)).
apply Res. trivial_in 4. unfold snd. unfold F_419. unfold F_405. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_405. unfold fst in HFabs1. unfold F_419 in HFabs1.   
pattern u2. simpl (plus _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 419 ] *)

unfold fst. unfold F_419.
auto.



	(* REWRITING on [ 411 ] *)

rename u1 into _u2. rename u2 into _u3. 
rename _u2 into u2. rename _u3 into u3. 
assert (H := Hind F_375).
assert (Res := Hind F_423). clear Hind.
assert (HFabs0 : fst (F_375 u3 u2)).
apply H. trivial_in 0. unfold snd. unfold F_375. unfold F_411. rewrite_model. abstract solve_rpo_mul.
unfold fst in HFabs0. unfold F_375 in HFabs0. simpl in HFabs0.

assert (HFabs1 : fst (F_423 u2 u3)).
apply Res. trivial_in 6. unfold snd. unfold F_423. unfold F_411. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_411. unfold fst in HFabs1. unfold F_423 in HFabs1.   
pattern u3, u2. simpl (plus _ _). cbv beta.
try rewrite  HFabs0.  simpl. auto.



	(* REWRITING on [ 423 ] *)

rename u1 into _u2. rename u2 into _u3. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_431). clear Hind.
assert (HFabs1 : fst (F_431 u2 u3)).
apply Res. trivial_in 7. unfold snd. unfold F_431. unfold F_423. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_423. unfold fst in HFabs1. unfold F_431 in HFabs1.   
pattern u3, u2. simpl (plus _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 431 ] *)

unfold fst. unfold F_431.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_375 := fun f => exists F, In F LF_375 /\ exists e1, exists e2, f = F e1 e2.

Theorem all_true_375: forall F, In F LF_375 -> forall u1: nat, forall u2: nat, fst (F u1  u2).
Proof.
let n := constr:(2) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_375);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_375;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_375: forall (u1: nat) (u2: nat), (plus u1 (S u2)) = (S (plus u1 u2)).
Proof.
do 2 intro.
apply (all_true_375 F_375);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_433_434 :=  nat -> (Prop * (List.list term)).

Definition F_434 : type_LF_433_434:= (fun  u1 => ((odd (S (plus u1 u1))) = true, (Term id_odd ((Term id_S ((Term id_plus ((model_nat u1):: (model_nat u1)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_449 : type_LF_433_434:= (fun  u1 => ((even (plus u1 u1)) = true -> true = true, (Term id_even ((Term id_plus ((model_nat u1):: (model_nat u1)::nil))::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_true nil)::nil)).
Definition F_453 : type_LF_433_434:= (fun  u1 => ((even (plus u1 u1)) = false -> false = true, (Term id_even ((Term id_plus ((model_nat u1):: (model_nat u1)::nil))::nil))::(Term id_false nil)::(Term id_false nil)::(Term id_true nil)::nil)).
Definition F_462 : type_LF_433_434:= (fun   _ => (true = false -> false = true, (Term id_true nil)::(Term id_false nil)::(Term id_false nil)::(Term id_true nil)::nil)).
Definition F_433 : type_LF_433_434:= (fun  u1 => ((even (plus u1 u1)) = true, (Term id_even ((Term id_plus ((model_nat u1):: (model_nat u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_473 : type_LF_433_434:= (fun   _ => ((even 0) = true, (Term id_even ((Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_493 : type_LF_433_434:= (fun   _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).
Definition F_479 : type_LF_433_434:= (fun  u2 => ((even (S (plus u2 (S u2)))) = true, (Term id_even ((Term id_S ((Term id_plus ((model_nat u2):: (Term id_S ((model_nat u2)::nil))::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_496 : type_LF_433_434:= (fun  u2 => ((even (S (S (plus u2 u2)))) = true, (Term id_even ((Term id_S ((Term id_S ((Term id_plus ((model_nat u2):: (model_nat u2)::nil))::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_510 : type_LF_433_434:= (fun  u2 => ((odd (S (plus u2 u2))) = true -> true = true, (Term id_odd ((Term id_S ((Term id_plus ((model_nat u2):: (model_nat u2)::nil))::nil))::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_true nil)::nil)).
Definition F_514 : type_LF_433_434:= (fun  u2 => ((odd (S (plus u2 u2))) = false -> false = true, (Term id_odd ((Term id_S ((Term id_plus ((model_nat u2):: (model_nat u2)::nil))::nil))::nil))::(Term id_false nil)::(Term id_false nil)::(Term id_true nil)::nil)).
Definition F_524 : type_LF_433_434:= (fun   _ => (true = false -> false = true, (Term id_true nil)::(Term id_false nil)::(Term id_false nil)::(Term id_true nil)::nil)).

Definition LF_433_434 := [F_434, F_449, F_453, F_462, F_433, F_473, F_493, F_479, F_496, F_510, F_514, F_524].


Function f_433 (u1: nat) {struct u1} : nat :=
 match u1 with
| 0 => 0
| (S u2) => 0
end.

Lemma main_433_434 : forall F, In F LF_433_434 -> forall u1, (forall F', In F' LF_433_434 -> forall e1, less (snd (F' e1)) (snd (F u1)) -> fst (F' e1)) -> fst (F u1).
Proof.
intros F HF u1; case_In HF; intro Hind.

	(* TOTAL CASE REWRITING on [ 434 ] *)

rename u1 into _u1. 
rename _u1 into u1. 
assert (H: ((even (plus u1 u1)) = true) \/ ((even (plus u1 u1)) = false)). 

destruct ((even (plus u1 u1))); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 32 ] *)

assert (H1 := Hind F_449). clear Hind.
assert (HFabs0 : fst (F_449 u1)).
apply H1. trivial_in 1. unfold snd. unfold F_449. unfold F_434. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_434. unfold F_449. unfold fst in HFabs0. unfold F_449 in HFabs0. simpl in HFabs0. 
pattern (plus u1 u1).
simpl (odd _). cbv beta. try unfold odd. try rewrite H. try rewrite H0. try unfold odd in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 33 ] *)

assert (H1 := Hind F_453). clear Hind.
assert (HFabs0 : fst (F_453 u1)).
apply H1. trivial_in 2. unfold snd. unfold F_453. unfold F_434. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_434. unfold F_453. unfold fst in HFabs0. unfold F_453 in HFabs0. simpl in HFabs0. 
pattern (plus u1 u1).
simpl (odd _). cbv beta. try unfold odd. try rewrite H. try rewrite H0. try unfold odd in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 449 ] *)

unfold fst. unfold F_449.
auto.



	(* REWRITING on [ 453 ] *)

rename u1 into _u1. 
rename _u1 into u1. 
assert (H := Hind F_433).
assert (Res := Hind F_462). clear Hind.
assert (HFabs0 : fst (F_433 u1)).
apply H. trivial_in 4. unfold snd. unfold F_433. unfold F_453. rewrite_model. abstract solve_rpo_mul.
unfold fst in HFabs0. unfold F_433 in HFabs0. simpl in HFabs0.

assert (HFabs1 : fst (F_462 0)).
apply Res. trivial_in 3. unfold snd. unfold F_462. unfold F_453. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_453. unfold fst in HFabs1. unfold F_462 in HFabs1.   
pattern u1. simpl (even _). cbv beta.
try rewrite  HFabs0.  simpl. auto.



	(* TAUTOLOGY on [ 462 ] *)

unfold fst. unfold F_462.
auto.



	(* GENERATE on [ 433 ] *)

rename u1 into _u1. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_433 u1). apply f_433_ind.

(* case [ 473 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_473). clear HFabs0.
assert (HFabs0 : fst (F_473 0)).
apply Hind. trivial_in 5. unfold snd. unfold F_473. unfold F_433. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_433. unfold F_473.
auto.


(* case [ 479 ] *)

intros _u1. intro u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_479). clear HFabs0.
assert (HFabs0 : fst (F_479 u2)).
apply Hind. trivial_in 7. unfold snd. unfold F_479. unfold F_433. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_433. unfold F_479.
auto.





	(* REWRITING on [ 473 ] *)

rename u1 into d_u1. 

assert (Res := Hind F_493). clear Hind.
assert (HFabs1 : fst (F_493 0)).
apply Res. trivial_in 6. unfold snd. unfold F_493. unfold F_473. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_473. unfold fst in HFabs1. unfold F_493 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 493 ] *)

unfold fst. unfold F_493.
auto.



	(* REWRITING on [ 479 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_496). clear Hind.
assert (HFabs1 : fst (F_496 u2)).
apply Res. trivial_in 8. unfold snd. unfold F_496. unfold F_479. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_479. unfold fst in HFabs1. unfold F_496 in HFabs1.  specialize true_375 with (u1 := u2) (u2 := u2). intro L. try rewrite L.
  simpl. auto.



	(* TOTAL CASE REWRITING on [ 496 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (H: ((odd (S (plus u2 u2))) = true) \/ ((odd (S (plus u2 u2))) = false)). 

destruct ((odd (S (plus u2 u2)))); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 29 ] *)

assert (H1 := Hind F_510). clear Hind.
assert (HFabs0 : fst (F_510 u2)).
apply H1. trivial_in 9. unfold snd. unfold F_510. unfold F_496. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_496. unfold F_510. unfold fst in HFabs0. unfold F_510 in HFabs0. simpl in HFabs0. 
pattern (S (plus u2 u2)).
simpl (even _). cbv beta. try unfold even. try rewrite H. try rewrite H0. try unfold even in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 30 ] *)

assert (H1 := Hind F_514). clear Hind.
assert (HFabs0 : fst (F_514 u2)).
apply H1. trivial_in 10. unfold snd. unfold F_514. unfold F_496. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_496. unfold F_514. unfold fst in HFabs0. unfold F_514 in HFabs0. simpl in HFabs0. 
pattern (S (plus u2 u2)).
simpl (even _). cbv beta. try unfold even. try rewrite H. try rewrite H0. try unfold even in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 510 ] *)

unfold fst. unfold F_510.
auto.



	(* REWRITING on [ 514 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (H := Hind F_434).
assert (Res := Hind F_524). clear Hind.
assert (HFabs0 : fst (F_434 u2)).
apply H. trivial_in 0. unfold snd. unfold F_434. unfold F_514. rewrite_model. abstract solve_rpo_mul.
unfold fst in HFabs0. unfold F_434 in HFabs0. simpl in HFabs0.

assert (HFabs1 : fst (F_524 0)).
apply Res. trivial_in 3. unfold snd. unfold F_524. unfold F_514. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_514. unfold fst in HFabs1. unfold F_524 in HFabs1.   
pattern u2. simpl (odd _). cbv beta.
try rewrite  HFabs0.  simpl. auto.



	(* TAUTOLOGY on [ 524 ] *)

unfold fst. unfold F_524.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_433_434 := fun f => exists F, In F LF_433_434 /\ exists e1, f = F e1.

Theorem all_true_433_434: forall F, In F LF_433_434 -> forall u1: nat, fst (F u1).
Proof.
let n := constr:(1) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_433_434);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_433_434;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_433: forall (u1: nat), (even (plus u1 u1)) = true.
Proof.
do 1 intro.
apply (all_true_433_434 F_433);
 (trivial_in 4) ||
 (repeat constructor).
Qed.




Theorem true_434: forall (u1: nat), (odd (S (plus u1 u1))) = true.
Proof.
do 1 intro.
apply (all_true_433_434 F_434);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_528 :=  nat ->  nat -> (Prop * (List.list term)).

Definition F_528 : type_LF_528:= (fun  u1 u2 => ((plus u1 u2) = (plus u2 u1), (Term id_plus ((model_nat u1):: (model_nat u2)::nil))::(Term id_plus ((model_nat u2):: (model_nat u1)::nil))::nil)).
Definition F_552 : type_LF_528:= (fun   _ _ => (0 = (plus 0 0), (Term id_0 nil)::(Term id_plus ((Term id_0 nil):: (Term id_0 nil)::nil))::nil)).
Definition F_558 : type_LF_528:= (fun  u3 _ => ((S u3) = (plus (S u3) 0), (Term id_S ((model_nat u3)::nil))::(Term id_plus ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::nil)).
Definition F_564 : type_LF_528:= (fun  u3 _ => ((S (plus u3 0)) = (plus 0 (S u3)), (Term id_S ((Term id_plus ((model_nat u3):: (Term id_0 nil)::nil))::nil))::(Term id_plus ((Term id_0 nil):: (Term id_S ((model_nat u3)::nil))::nil))::nil)).
Definition F_570 : type_LF_528:= (fun  u3 u4 => ((S (plus u3 (S u4))) = (plus (S u4) (S u3)), (Term id_S ((Term id_plus ((model_nat u3):: (Term id_S ((model_nat u4)::nil))::nil))::nil))::(Term id_plus ((Term id_S ((model_nat u4)::nil)):: (Term id_S ((model_nat u3)::nil))::nil))::nil)).
Definition F_597 : type_LF_528:= (fun  u3 _ => ((S u3) = (plus 0 (S u3)), (Term id_S ((model_nat u3)::nil))::(Term id_plus ((Term id_0 nil):: (Term id_S ((model_nat u3)::nil))::nil))::nil)).
Definition F_619 : type_LF_528:= (fun  u3 _ => ((S u3) = (S u3), (Term id_S ((model_nat u3)::nil))::(Term id_S ((model_nat u3)::nil))::nil)).
Definition F_608 : type_LF_528:= (fun  u3 u4 => ((S (S (plus u3 u4))) = (plus (S u4) (S u3)), (Term id_S ((Term id_S ((Term id_plus ((model_nat u3):: (model_nat u4)::nil))::nil))::nil))::(Term id_plus ((Term id_S ((model_nat u4)::nil)):: (Term id_S ((model_nat u3)::nil))::nil))::nil)).
Definition F_624 : type_LF_528:= (fun  u3 u4 => ((S (S (plus u3 u4))) = (S (plus u4 (S u3))), (Term id_S ((Term id_S ((Term id_plus ((model_nat u3):: (model_nat u4)::nil))::nil))::nil))::(Term id_S ((Term id_plus ((model_nat u4):: (Term id_S ((model_nat u3)::nil))::nil))::nil))::nil)).
Definition F_632 : type_LF_528:= (fun  u3 u4 => ((S (plus u3 u4)) = (plus u4 (S u3)), (Term id_S ((Term id_plus ((model_nat u3):: (model_nat u4)::nil))::nil))::(Term id_plus ((model_nat u4):: (Term id_S ((model_nat u3)::nil))::nil))::nil)).
Definition F_642 : type_LF_528:= (fun  u3 u4 => ((S (plus u3 u4)) = (S (plus u4 u3)), (Term id_S ((Term id_plus ((model_nat u3):: (model_nat u4)::nil))::nil))::(Term id_S ((Term id_plus ((model_nat u4):: (model_nat u3)::nil))::nil))::nil)).

Definition LF_528 := [F_528, F_552, F_558, F_564, F_570, F_597, F_619, F_608, F_624, F_632, F_642].


Function f_528 (u1: nat) (u2: nat) {struct u1} : nat :=
 match u1, u2 with
| 0, 0 => 0
| 0, (S u3) => 0
| (S u3), 0 => 0
| (S u3), (S u4) => 0
end.

Lemma main_528 : forall F, In F LF_528 -> forall u1, forall u2, (forall F', In F' LF_528 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 528 ] *)

rename u1 into _u1. rename u2 into _u2. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_528 u1 u2). apply f_528_ind.

(* case [ 552 ] *)

intros _u1 _u2.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_552). clear HFabs0.
assert (HFabs0 : fst (F_552 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_552. unfold F_528. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_528. unfold F_552.
auto.


(* case [ 558 ] *)

intros _u1 _u2.  intro eq_1. intro u3.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_558). clear HFabs0.
assert (HFabs0 : fst (F_558 u3 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_558. unfold F_528. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_528. unfold F_558.
auto.


(* case [ 564 ] *)

intros _u1 _u2. intro u3.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_564). clear HFabs0.
assert (HFabs0 : fst (F_564 u3 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_564. unfold F_528. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_528. unfold F_564.
auto.


(* case [ 570 ] *)

intros _u1 _u2. intro u3.  intro eq_1. intro u4.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_570). clear HFabs0.
assert (HFabs0 : fst (F_570 u3 u4)).
apply Hind. trivial_in 4. unfold snd. unfold F_570. unfold F_528. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_528. unfold F_570.
auto.





	(* SUBSUMPTION on [ 552 ] *)

rename u1 into d_u1. rename u2 into d_u2. 

unfold fst. unfold F_552. specialize true_347 with (u1 := 0).
(auto || symmetry; auto).



	(* SUBSUMPTION on [ 558 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
unfold fst. unfold F_558. specialize true_347 with (u1 := (S u3)).
(auto || symmetry; auto).



	(* REWRITING on [ 564 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (Res := Hind F_597). clear Hind.
assert (HFabs1 : fst (F_597 u3 0)).
apply Res. trivial_in 5. unfold snd. unfold F_597. unfold F_564. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_564. unfold fst in HFabs1. unfold F_597 in HFabs1.  specialize true_347 with (u1 := u3). intro L. try rewrite L.
  simpl. auto.



	(* REWRITING on [ 570 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_608). clear Hind.
assert (HFabs1 : fst (F_608 u3 u4)).
apply Res. trivial_in 7. unfold snd. unfold F_608. unfold F_570. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_570. unfold fst in HFabs1. unfold F_608 in HFabs1.  specialize true_375 with (u1 := u3) (u2 := u4). intro L. try rewrite L.
  simpl. auto.



	(* REWRITING on [ 597 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (Res := Hind F_619). clear Hind.
assert (HFabs1 : fst (F_619 u3 0)).
apply Res. trivial_in 6. unfold snd. unfold F_619. unfold F_597. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_597. unfold fst in HFabs1. unfold F_619 in HFabs1.   
pattern (S u3). simpl (plus _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 619 ] *)

unfold fst. unfold F_619.
auto.



	(* REWRITING on [ 608 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_624). clear Hind.
assert (HFabs1 : fst (F_624 u3 u4)).
apply Res. trivial_in 8. unfold snd. unfold F_624. unfold F_608. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_608. unfold fst in HFabs1. unfold F_624 in HFabs1.   
pattern u4, (S u3). simpl (plus _ _). cbv beta.
 simpl. auto.



	(* POSITIVE DECOMPOSITION on [ 624 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (H1 := Hind F_632). 
assert (HFabs1 : fst (F_632 u3 u4)).
apply H1. trivial_in 9. unfold snd. unfold F_632. unfold F_624. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_624. unfold F_632.

unfold fst in HFabs1. unfold F_632 in HFabs1.

repeat (auto || (rewrite HFabs1||  auto)).


	(* REWRITING on [ 632 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_642). clear Hind.
assert (HFabs1 : fst (F_642 u3 u4)).
apply Res. trivial_in 10. unfold snd. unfold F_642. unfold F_632. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_632. unfold fst in HFabs1. unfold F_642 in HFabs1.  specialize true_375 with (u1 := u4) (u2 := u3). intro L. try rewrite L.
  simpl. auto.



	(* POSITIVE DECOMPOSITION on [ 642 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (H1 := Hind F_528). 
assert (HFabs1 : fst (F_528 u3 u4)).
apply H1. trivial_in 0. unfold snd. unfold F_528. unfold F_642. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_642. unfold F_528.

unfold fst in HFabs1. unfold F_528 in HFabs1.

repeat (auto || (rewrite HFabs1||  auto)).


Qed.



(* the set of all formula instances from the proof *)
Definition S_528 := fun f => exists F, In F LF_528 /\ exists e1, exists e2, f = F e1 e2.

Theorem all_true_528: forall F, In F LF_528 -> forall u1: nat, forall u2: nat, fst (F u1  u2).
Proof.
let n := constr:(2) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_528);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_528;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_528: forall (u1: nat) (u2: nat), (plus u1 u2) = (plus u2 u1).
Proof.
do 2 intro.
apply (all_true_528 F_528);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_660_661 :=  nat -> (Prop * (List.list term)).

Definition F_660 : type_LF_660_661:= (fun  u1 => ((evenm (plus u1 u1)) = true, (Term id_evenm ((Term id_plus ((model_nat u1):: (model_nat u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_687 : type_LF_660_661:= (fun   _ => ((evenm 0) = true, (Term id_evenm ((Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_713 : type_LF_660_661:= (fun   _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).
Definition F_693 : type_LF_660_661:= (fun  u2 => ((evenm (S (plus u2 (S u2)))) = true, (Term id_evenm ((Term id_S ((Term id_plus ((model_nat u2):: (Term id_S ((model_nat u2)::nil))::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_716 : type_LF_660_661:= (fun  u2 => ((oddm (plus u2 (S u2))) = true, (Term id_oddm ((Term id_plus ((model_nat u2):: (Term id_S ((model_nat u2)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_728 : type_LF_660_661:= (fun  u2 => ((oddm (S (plus u2 u2))) = true, (Term id_oddm ((Term id_S ((Term id_plus ((model_nat u2):: (model_nat u2)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_661 : type_LF_660_661:= (fun  u1 => ((oddm (plus u1 u1)) = false, (Term id_oddm ((Term id_plus ((model_nat u1):: (model_nat u1)::nil))::nil))::(Term id_false nil)::nil)).
Definition F_760 : type_LF_660_661:= (fun   _ => ((oddm 0) = false, (Term id_oddm ((Term id_0 nil)::nil))::(Term id_false nil)::nil)).
Definition F_786 : type_LF_660_661:= (fun   _ => (false = false, (Term id_false nil)::(Term id_false nil)::nil)).
Definition F_766 : type_LF_660_661:= (fun  u2 => ((oddm (S (plus u2 (S u2)))) = false, (Term id_oddm ((Term id_S ((Term id_plus ((model_nat u2):: (Term id_S ((model_nat u2)::nil))::nil))::nil))::nil))::(Term id_false nil)::nil)).
Definition F_789 : type_LF_660_661:= (fun  u2 => ((evenm (plus u2 (S u2))) = false, (Term id_evenm ((Term id_plus ((model_nat u2):: (Term id_S ((model_nat u2)::nil))::nil))::nil))::(Term id_false nil)::nil)).
Definition F_801 : type_LF_660_661:= (fun  u2 => ((evenm (S (plus u2 u2))) = false, (Term id_evenm ((Term id_S ((Term id_plus ((model_nat u2):: (model_nat u2)::nil))::nil))::nil))::(Term id_false nil)::nil)).

Definition LF_660_661 := [F_660, F_687, F_713, F_693, F_716, F_728, F_661, F_760, F_786, F_766, F_789, F_801].


Function f_660 (u1: nat) {struct u1} : nat :=
 match u1 with
| 0 => 0
| (S u2) => 0
end.

Function f_661 (u1: nat) {struct u1} : nat :=
 match u1 with
| 0 => 0
| (S u2) => 0
end.

Lemma main_660_661 : forall F, In F LF_660_661 -> forall u1, (forall F', In F' LF_660_661 -> forall e1, less (snd (F' e1)) (snd (F u1)) -> fst (F' e1)) -> fst (F u1).
Proof.
intros F HF u1; case_In HF; intro Hind.

	(* GENERATE on [ 660 ] *)

rename u1 into _u1. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_660 u1). apply f_660_ind.

(* case [ 687 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_687). clear HFabs0.
assert (HFabs0 : fst (F_687 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_687. unfold F_660. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_660. unfold F_687.
auto.


(* case [ 693 ] *)

intros _u1. intro u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_693). clear HFabs0.
assert (HFabs0 : fst (F_693 u2)).
apply Hind. trivial_in 3. unfold snd. unfold F_693. unfold F_660. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_660. unfold F_693.
auto.





	(* REWRITING on [ 687 ] *)

rename u1 into d_u1. 

assert (Res := Hind F_713). clear Hind.
assert (HFabs1 : fst (F_713 0)).
apply Res. trivial_in 2. unfold snd. unfold F_713. unfold F_687. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_687. unfold fst in HFabs1. unfold F_713 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 713 ] *)

unfold fst. unfold F_713.
auto.



	(* REWRITING on [ 693 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_716). clear Hind.
assert (HFabs1 : fst (F_716 u2)).
apply Res. trivial_in 4. unfold snd. unfold F_716. unfold F_693. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_693. unfold fst in HFabs1. unfold F_716 in HFabs1.   
pattern (plus u2 (S u2)). simpl (evenm _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 716 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_728). clear Hind.
assert (HFabs1 : fst (F_728 u2)).
apply Res. trivial_in 5. unfold snd. unfold F_728. unfold F_716. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_716. unfold fst in HFabs1. unfold F_728 in HFabs1.  specialize true_375 with (u1 := u2) (u2 := u2). intro L. try rewrite L.
  simpl. auto.



	(* REWRITING on [ 728 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_660). clear Hind.
assert (HFabs1 : fst (F_660 u2)).
apply Res. trivial_in 0. unfold snd. unfold F_660. unfold F_728. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_728. unfold fst in HFabs1. unfold F_660 in HFabs1.   
pattern (plus u2 u2). simpl (oddm _). cbv beta.
 simpl. auto.



	(* GENERATE on [ 661 ] *)

rename u1 into _u1. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_661 u1). apply f_661_ind.

(* case [ 760 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_760). clear HFabs0.
assert (HFabs0 : fst (F_760 0)).
apply Hind. trivial_in 7. unfold snd. unfold F_760. unfold F_661. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_661. unfold F_760.
auto.


(* case [ 766 ] *)

intros _u1. intro u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_766). clear HFabs0.
assert (HFabs0 : fst (F_766 u2)).
apply Hind. trivial_in 9. unfold snd. unfold F_766. unfold F_661. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_661. unfold F_766.
auto.





	(* REWRITING on [ 760 ] *)

rename u1 into d_u1. 

assert (Res := Hind F_786). clear Hind.
assert (HFabs1 : fst (F_786 0)).
apply Res. trivial_in 8. unfold snd. unfold F_786. unfold F_760. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_760. unfold fst in HFabs1. unfold F_786 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 786 ] *)

unfold fst. unfold F_786.
auto.



	(* REWRITING on [ 766 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_789). clear Hind.
assert (HFabs1 : fst (F_789 u2)).
apply Res. trivial_in 10. unfold snd. unfold F_789. unfold F_766. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_766. unfold fst in HFabs1. unfold F_789 in HFabs1.   
pattern (plus u2 (S u2)). simpl (oddm _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 789 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_801). clear Hind.
assert (HFabs1 : fst (F_801 u2)).
apply Res. trivial_in 11. unfold snd. unfold F_801. unfold F_789. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_789. unfold fst in HFabs1. unfold F_801 in HFabs1.  specialize true_375 with (u1 := u2) (u2 := u2). intro L. try rewrite L.
  simpl. auto.



	(* REWRITING on [ 801 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_661). clear Hind.
assert (HFabs1 : fst (F_661 u2)).
apply Res. trivial_in 6. unfold snd. unfold F_661. unfold F_801. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_801. unfold fst in HFabs1. unfold F_661 in HFabs1.   
pattern (plus u2 u2). simpl (evenm _). cbv beta.
 simpl. auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_660_661 := fun f => exists F, In F LF_660_661 /\ exists e1, f = F e1.

Theorem all_true_660_661: forall F, In F LF_660_661 -> forall u1: nat, fst (F u1).
Proof.
let n := constr:(1) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_660_661);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_660_661;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_660: forall (u1: nat), (evenm (plus u1 u1)) = true.
Proof.
do 1 intro.
apply (all_true_660_661 F_660);
 (trivial_in 0) ||
 (repeat constructor).
Qed.




Theorem true_661: forall (u1: nat), (oddm (plus u1 u1)) = false.
Proof.
do 1 intro.
apply (all_true_660_661 F_661);
 (trivial_in 6) ||
 (repeat constructor).
Qed.


Definition type_LF_825 :=  nat -> (Prop * (List.list term)).

Definition F_825 : type_LF_825:= (fun  u1 => ((evenr (S u1)) = true -> true = (oddm u1), (Term id_evenr ((Term id_S ((model_nat u1)::nil))::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_oddm ((model_nat u1)::nil))::nil)).
Definition F_845 : type_LF_825:= (fun   _ => (false = true -> true = (oddm 0), (Term id_false nil)::(Term id_true nil)::(Term id_true nil)::(Term id_oddm ((Term id_0 nil)::nil))::nil)).
Definition F_851 : type_LF_825:= (fun  u2 => ((evenr u2) = true -> true = (oddm (S u2)), (Term id_evenr ((model_nat u2)::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_oddm ((Term id_S ((model_nat u2)::nil))::nil))::nil)).
Definition F_864 : type_LF_825:= (fun  u2 => ((evenr u2) = true -> true = (evenm u2), (Term id_evenr ((model_nat u2)::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_evenm ((model_nat u2)::nil))::nil)).
Definition F_894 : type_LF_825:= (fun   _ => (false = true -> true = (evenm (S 0)), (Term id_false nil)::(Term id_true nil)::(Term id_true nil)::(Term id_evenm ((Term id_S ((Term id_0 nil)::nil))::nil))::nil)).
Definition F_888 : type_LF_825:= (fun   _ => (true = true -> true = (evenm 0), (Term id_true nil)::(Term id_true nil)::(Term id_true nil)::(Term id_evenm ((Term id_0 nil)::nil))::nil)).
Definition F_900 : type_LF_825:= (fun  u3 => ((evenr u3) = true -> true = (evenm (S (S u3))), (Term id_evenr ((model_nat u3)::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_evenm ((Term id_S ((Term id_S ((model_nat u3)::nil))::nil))::nil))::nil)).
Definition F_927 : type_LF_825:= (fun   _ => (true = (evenm 0), (Term id_true nil)::(Term id_evenm ((Term id_0 nil)::nil))::nil)).
Definition F_961 : type_LF_825:= (fun   _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).

Definition LF_825 := [F_825, F_845, F_851, F_864, F_894, F_888, F_900, F_927, F_961].


Function f_825 (u1: nat) {struct u1} : bool :=
 match u1 with
| 0 => true
| (S u2) => true
end.

Function f_864 (u2: nat) {struct u2} : bool :=
 match u2 with
| 0 => true
| (S 0) => true
| (S (S u3)) => true
end.

Lemma main_825 : forall F, In F LF_825 -> forall u1, (forall F', In F' LF_825 -> forall e1, less (snd (F' e1)) (snd (F u1)) -> fst (F' e1)) -> fst (F u1).
Proof.
intros F HF u1; case_In HF; intro Hind.

	(* GENERATE on [ 825 ] *)

rename u1 into _u1. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_825 u1). apply f_825_ind.

(* case [ 845 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_845). clear HFabs0.
assert (HFabs0 : fst (F_845 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_845. unfold F_825. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_825. unfold F_845.
auto.


(* case [ 851 ] *)

intros _u1. intro u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_851). clear HFabs0.
assert (HFabs0 : fst (F_851 u2)).
apply Hind. trivial_in 2. unfold snd. unfold F_851. unfold F_825. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_825. unfold F_851.
auto.





	(* NEGATIVE CLASH on [ 845 ] *)

unfold fst. unfold F_845. intros. try discriminate.



	(* REWRITING on [ 851 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_864). clear Hind.
assert (HFabs1 : fst (F_864 u2)).
apply Res. trivial_in 3. unfold snd. unfold F_864. unfold F_851. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_851. unfold fst in HFabs1. unfold F_864 in HFabs1.   
pattern u2. simpl (oddm _). cbv beta.
 simpl. auto.



	(* GENERATE on [ 864 ] *)

rename u1 into _u2. 
rename _u2 into u2. 

revert Hind.

pattern u2, (f_864 u2). apply f_864_ind.

(* case [ 888 ] *)

intros _u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_888). clear HFabs0.
assert (HFabs0 : fst (F_888 0)).
apply Hind. trivial_in 5. unfold snd. unfold F_888. unfold F_864. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_864. unfold F_888.
auto.


(* case [ 894 ] *)

intros _u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_894). clear HFabs0.
assert (HFabs0 : fst (F_894 0)).
apply Hind. trivial_in 4. unfold snd. unfold F_894. unfold F_864. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_864. unfold F_894.
auto.


(* case [ 900 ] *)

intros _u2. intro u3.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_900). clear HFabs0.
assert (HFabs0 : fst (F_900 u3)).
apply Hind. trivial_in 6. unfold snd. unfold F_900. unfold F_864. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_864. unfold F_900.
auto.





	(* NEGATIVE CLASH on [ 894 ] *)

unfold fst. unfold F_894. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 888 ] *)

rename u1 into d_u1. 

assert (H := Hind F_927). 
assert (HFabs0 : fst (F_927 0)).
apply H. trivial_in 7. unfold snd. unfold F_927. unfold F_888. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_888. unfold F_927.

unfold fst in HFabs0. unfold F_927 in HFabs0.
auto.



	(* REWRITING on [ 900 ] *)

rename u1 into _u3. 
rename _u3 into u3. 
assert (Res := Hind F_851). clear Hind.
assert (HFabs1 : fst (F_851 u3)).
apply Res. trivial_in 2. unfold snd. unfold F_851. unfold F_900. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_900. unfold fst in HFabs1. unfold F_851 in HFabs1.   
pattern (S u3). simpl (evenm _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 927 ] *)

rename u1 into d_u1. 

assert (Res := Hind F_961). clear Hind.
assert (HFabs1 : fst (F_961 0)).
apply Res. trivial_in 8. unfold snd. unfold F_961. unfold F_927. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_927. unfold fst in HFabs1. unfold F_961 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 961 ] *)

unfold fst. unfold F_961.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_825 := fun f => exists F, In F LF_825 /\ exists e1, f = F e1.

Theorem all_true_825: forall F, In F LF_825 -> forall u1: nat, fst (F u1).
Proof.
let n := constr:(1) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_825);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_825;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_825: forall (u1: nat), (evenr (S u1)) = true -> true = (oddm u1).
Proof.
do 1 intro.
apply (all_true_825 F_825);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_962 :=  nat -> (Prop * (List.list term)).

Definition F_962 : type_LF_962:= (fun  u1 => ((oddc u1) = (oddm u1), (Term id_oddc ((model_nat u1)::nil))::(Term id_oddm ((model_nat u1)::nil))::nil)).
Definition F_978 : type_LF_962:= (fun  u1 => ((evenr u1) = true -> false = (oddm u1), (Term id_evenr ((model_nat u1)::nil))::(Term id_true nil)::(Term id_false nil)::(Term id_oddm ((model_nat u1)::nil))::nil)).
Definition F_1024 : type_LF_962:= (fun   _ => (false = true -> false = (oddm (S 0)), (Term id_false nil)::(Term id_true nil)::(Term id_false nil)::(Term id_oddm ((Term id_S ((Term id_0 nil)::nil))::nil))::nil)).
Definition F_1018 : type_LF_962:= (fun   _ => (true = true -> false = (oddm 0), (Term id_true nil)::(Term id_true nil)::(Term id_false nil)::(Term id_oddm ((Term id_0 nil)::nil))::nil)).
Definition F_1030 : type_LF_962:= (fun  u2 => ((evenr u2) = true -> false = (oddm (S (S u2))), (Term id_evenr ((model_nat u2)::nil))::(Term id_true nil)::(Term id_false nil)::(Term id_oddm ((Term id_S ((Term id_S ((model_nat u2)::nil))::nil))::nil))::nil)).
Definition F_1059 : type_LF_962:= (fun   _ => (false = (oddm 0), (Term id_false nil)::(Term id_oddm ((Term id_0 nil)::nil))::nil)).
Definition F_1093 : type_LF_962:= (fun   _ => (false = false, (Term id_false nil)::(Term id_false nil)::nil)).
Definition F_1076 : type_LF_962:= (fun  u2 => ((evenr u2) = true -> false = (evenm (S u2)), (Term id_evenr ((model_nat u2)::nil))::(Term id_true nil)::(Term id_false nil)::(Term id_evenm ((Term id_S ((model_nat u2)::nil))::nil))::nil)).
Definition F_982 : type_LF_962:= (fun  u1 => ((evenr u1) = false -> true = (oddm u1), (Term id_evenr ((model_nat u1)::nil))::(Term id_false nil)::(Term id_true nil)::(Term id_oddm ((model_nat u1)::nil))::nil)).
Definition F_1123 : type_LF_962:= (fun   _ => (true = false -> true = (oddm 0), (Term id_true nil)::(Term id_false nil)::(Term id_true nil)::(Term id_oddm ((Term id_0 nil)::nil))::nil)).
Definition F_1129 : type_LF_962:= (fun   _ => (false = false -> true = (oddm (S 0)), (Term id_false nil)::(Term id_false nil)::(Term id_true nil)::(Term id_oddm ((Term id_S ((Term id_0 nil)::nil))::nil))::nil)).
Definition F_1135 : type_LF_962:= (fun  u2 => ((evenr u2) = false -> true = (oddm (S (S u2))), (Term id_evenr ((model_nat u2)::nil))::(Term id_false nil)::(Term id_true nil)::(Term id_oddm ((Term id_S ((Term id_S ((model_nat u2)::nil))::nil))::nil))::nil)).
Definition F_1164 : type_LF_962:= (fun   _ => (true = (oddm (S 0)), (Term id_true nil)::(Term id_oddm ((Term id_S ((Term id_0 nil)::nil))::nil))::nil)).
Definition F_1181 : type_LF_962:= (fun  u2 => ((evenr u2) = false -> true = (evenm (S u2)), (Term id_evenr ((model_nat u2)::nil))::(Term id_false nil)::(Term id_true nil)::(Term id_evenm ((Term id_S ((model_nat u2)::nil))::nil))::nil)).
Definition F_1198 : type_LF_962:= (fun   _ => (true = (evenm 0), (Term id_true nil)::(Term id_evenm ((Term id_0 nil)::nil))::nil)).
Definition F_1233 : type_LF_962:= (fun   _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).

Definition LF_962 := [F_962, F_978, F_1024, F_1018, F_1030, F_1059, F_1093, F_1076, F_982, F_1123, F_1129, F_1135, F_1164, F_1181, F_1198, F_1233].


Function f_978 (u1: nat) {struct u1} : bool :=
 match u1 with
| 0 => true
| (S 0) => true
| (S (S u2)) => true
end.

Function f_982 (u1: nat) {struct u1} : bool :=
 match u1 with
| 0 => true
| (S 0) => true
| (S (S u2)) => true
end.

Lemma main_962 : forall F, In F LF_962 -> forall u1, (forall F', In F' LF_962 -> forall e1, less (snd (F' e1)) (snd (F u1)) -> fst (F' e1)) -> fst (F u1).
Proof.
intros F HF u1; case_In HF; intro Hind.

	(* TOTAL CASE REWRITING on [ 962 ] *)

rename u1 into _u1. 
rename _u1 into u1. 
assert (H: ((evenr u1) = true) \/ ((evenr u1) = false)). 

destruct ((evenr u1)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 22 ] *)

assert (H1 := Hind F_978). clear Hind.
assert (HFabs0 : fst (F_978 u1)).
apply H1. trivial_in 1. unfold snd. unfold F_978. unfold F_962. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_962. unfold F_978. unfold fst in HFabs0. unfold F_978 in HFabs0. simpl in HFabs0. 
pattern u1.
simpl (oddc _). cbv beta. try unfold oddc. try rewrite H. try rewrite H0. try unfold oddc in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 23 ] *)

assert (H1 := Hind F_982). clear Hind.
assert (HFabs0 : fst (F_982 u1)).
apply H1. trivial_in 8. unfold snd. unfold F_982. unfold F_962. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_962. unfold F_982. unfold fst in HFabs0. unfold F_982 in HFabs0. simpl in HFabs0. 
pattern u1.
simpl (oddc _). cbv beta. try unfold oddc. try rewrite H. try rewrite H0. try unfold oddc in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* GENERATE on [ 978 ] *)

rename u1 into _u1. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_978 u1). apply f_978_ind.

(* case [ 1018 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_1018). clear HFabs0.
assert (HFabs0 : fst (F_1018 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_1018. unfold F_978. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_978. unfold F_1018.
auto.


(* case [ 1024 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_1024). clear HFabs0.
assert (HFabs0 : fst (F_1024 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_1024. unfold F_978. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_978. unfold F_1024.
auto.


(* case [ 1030 ] *)

intros _u1. intro u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_1030). clear HFabs0.
assert (HFabs0 : fst (F_1030 u2)).
apply Hind. trivial_in 4. unfold snd. unfold F_1030. unfold F_978. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_978. unfold F_1030.
auto.





	(* NEGATIVE CLASH on [ 1024 ] *)

unfold fst. unfold F_1024. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 1018 ] *)

rename u1 into d_u1. 

assert (H := Hind F_1059). 
assert (HFabs0 : fst (F_1059 0)).
apply H. trivial_in 5. unfold snd. unfold F_1059. unfold F_1018. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1018. unfold F_1059.

unfold fst in HFabs0. unfold F_1059 in HFabs0.
auto.



	(* REWRITING on [ 1030 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_1076). clear Hind.
assert (HFabs1 : fst (F_1076 u2)).
apply Res. trivial_in 7. unfold snd. unfold F_1076. unfold F_1030. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1030. unfold fst in HFabs1. unfold F_1076 in HFabs1.   
pattern (S u2). simpl (oddm _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1059 ] *)

rename u1 into d_u1. 

assert (Res := Hind F_1093). clear Hind.
assert (HFabs1 : fst (F_1093 0)).
apply Res. trivial_in 6. unfold snd. unfold F_1093. unfold F_1059. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1059. unfold fst in HFabs1. unfold F_1093 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 1093 ] *)

unfold fst. unfold F_1093.
auto.



	(* REWRITING on [ 1076 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_978). clear Hind.
assert (HFabs1 : fst (F_978 u2)).
apply Res. trivial_in 1. unfold snd. unfold F_978. unfold F_1076. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1076. unfold fst in HFabs1. unfold F_978 in HFabs1.   
pattern u2. simpl (evenm _). cbv beta.
 simpl. auto.



	(* GENERATE on [ 982 ] *)

rename u1 into _u1. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_982 u1). apply f_982_ind.

(* case [ 1123 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_1123). clear HFabs0.
assert (HFabs0 : fst (F_1123 0)).
apply Hind. trivial_in 9. unfold snd. unfold F_1123. unfold F_982. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_982. unfold F_1123.
auto.


(* case [ 1129 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_1129). clear HFabs0.
assert (HFabs0 : fst (F_1129 0)).
apply Hind. trivial_in 10. unfold snd. unfold F_1129. unfold F_982. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_982. unfold F_1129.
auto.


(* case [ 1135 ] *)

intros _u1. intro u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_1135). clear HFabs0.
assert (HFabs0 : fst (F_1135 u2)).
apply Hind. trivial_in 11. unfold snd. unfold F_1135. unfold F_982. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_982. unfold F_1135.
auto.





	(* NEGATIVE CLASH on [ 1123 ] *)

unfold fst. unfold F_1123. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 1129 ] *)

rename u1 into d_u1. 

assert (H := Hind F_1164). 
assert (HFabs0 : fst (F_1164 0)).
apply H. trivial_in 12. unfold snd. unfold F_1164. unfold F_1129. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1129. unfold F_1164.

unfold fst in HFabs0. unfold F_1164 in HFabs0.
auto.



	(* REWRITING on [ 1135 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_1181). clear Hind.
assert (HFabs1 : fst (F_1181 u2)).
apply Res. trivial_in 13. unfold snd. unfold F_1181. unfold F_1135. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1135. unfold fst in HFabs1. unfold F_1181 in HFabs1.   
pattern (S u2). simpl (oddm _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1164 ] *)

rename u1 into d_u1. 

assert (Res := Hind F_1198). clear Hind.
assert (HFabs1 : fst (F_1198 0)).
apply Res. trivial_in 14. unfold snd. unfold F_1198. unfold F_1164. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1164. unfold fst in HFabs1. unfold F_1198 in HFabs1.   
pattern 0. simpl (oddm _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1181 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (Res := Hind F_982). clear Hind.
assert (HFabs1 : fst (F_982 u2)).
apply Res. trivial_in 8. unfold snd. unfold F_982. unfold F_1181. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1181. unfold fst in HFabs1. unfold F_982 in HFabs1.   
pattern u2. simpl (evenm _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1198 ] *)

rename u1 into d_u1. 

assert (Res := Hind F_1233). clear Hind.
assert (HFabs1 : fst (F_1233 0)).
apply Res. trivial_in 15. unfold snd. unfold F_1233. unfold F_1198. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1198. unfold fst in HFabs1. unfold F_1233 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 1233 ] *)

unfold fst. unfold F_1233.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_962 := fun f => exists F, In F LF_962 /\ exists e1, f = F e1.

Theorem all_true_962: forall F, In F LF_962 -> forall u1: nat, fst (F u1).
Proof.
let n := constr:(1) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_962);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_962;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_962: forall (u1: nat), (oddc u1) = (oddm u1).
Proof.
do 1 intro.
apply (all_true_962 F_962);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_1234 :=  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_1234 : type_LF_1234:= (fun  u1 u2 u3 => ((plus u1 (plus u2 u3)) = (plus (plus u1 u2) u3), (Term id_plus ((model_nat u1):: (Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_plus ((Term id_plus ((model_nat u1):: (model_nat u2)::nil)):: (model_nat u3)::nil))::nil)).
Definition F_1255 : type_LF_1234:= (fun  u2 u3 _ => ((plus u2 u3) = (plus (plus 0 u2) u3), (Term id_plus ((model_nat u2):: (model_nat u3)::nil))::(Term id_plus ((Term id_plus ((Term id_0 nil):: (model_nat u2)::nil)):: (model_nat u3)::nil))::nil)).
Definition F_1290 : type_LF_1234:= (fun  u2 u3 _ => ((plus u2 u3) = (plus u2 u3), (Term id_plus ((model_nat u2):: (model_nat u3)::nil))::(Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil)).
Definition F_1261 : type_LF_1234:= (fun  u2 u3 u4 => ((S (plus u4 (plus u2 u3))) = (plus (plus (S u4) u2) u3), (Term id_S ((Term id_plus ((model_nat u4):: (Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::nil))::(Term id_plus ((Term id_plus ((Term id_S ((model_nat u4)::nil)):: (model_nat u2)::nil)):: (model_nat u3)::nil))::nil)).
Definition F_1294 : type_LF_1234:= (fun  u2 u3 u4 => ((S (plus u4 (plus u2 u3))) = (plus (S (plus u4 u2)) u3), (Term id_S ((Term id_plus ((model_nat u4):: (Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::nil))::(Term id_plus ((Term id_S ((Term id_plus ((model_nat u4):: (model_nat u2)::nil))::nil)):: (model_nat u3)::nil))::nil)).
Definition F_1309 : type_LF_1234:= (fun  u2 u3 u4 => ((S (plus u4 (plus u2 u3))) = (S (plus (plus u4 u2) u3)), (Term id_S ((Term id_plus ((model_nat u4):: (Term id_plus ((model_nat u2):: (model_nat u3)::nil))::nil))::nil))::(Term id_S ((Term id_plus ((Term id_plus ((model_nat u4):: (model_nat u2)::nil)):: (model_nat u3)::nil))::nil))::nil)).

Definition LF_1234 := [F_1234, F_1255, F_1290, F_1261, F_1294, F_1309].


Function f_1234 (u1: nat) (u2: nat) (u3: nat) {struct u1} : nat :=
 match u1, u2, u3 with
| 0, _, _ => 0
| (S u4), _, _ => 0
end.

Lemma main_1234 : forall F, In F LF_1234 -> forall u1, forall u2, forall u3, (forall F', In F' LF_1234 -> forall e1, forall e2, forall e3, less (snd (F' e1 e2 e3)) (snd (F u1 u2 u3)) -> fst (F' e1 e2 e3)) -> fst (F u1 u2 u3).
Proof.
intros F HF u1 u2 u3; case_In HF; intro Hind.

	(* GENERATE on [ 1234 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. 

revert Hind.

pattern u1, u2, u3, (f_1234 u1 u2 u3). apply f_1234_ind.

(* case [ 1255 ] *)

intros _u1 _u2 _u3.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_1255). clear HFabs0.
assert (HFabs0 : fst (F_1255 _u2 _u3 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_1255. unfold F_1234. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1234. unfold F_1255.
auto.


(* case [ 1261 ] *)

intros _u1 _u2 _u3. intro u4.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_1261). clear HFabs0.
assert (HFabs0 : fst (F_1261 _u2 _u3 u4)).
apply Hind. trivial_in 3. unfold snd. unfold F_1261. unfold F_1234. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1234. unfold F_1261.
auto.





	(* REWRITING on [ 1255 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into d_u3. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_1290). clear Hind.
assert (HFabs1 : fst (F_1290 u2 u3 0)).
apply Res. trivial_in 2. unfold snd. unfold F_1290. unfold F_1255. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1255. unfold fst in HFabs1. unfold F_1290 in HFabs1.   
pattern u2. simpl (plus _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 1290 ] *)

unfold fst. unfold F_1290.
auto.



	(* REWRITING on [ 1261 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_1294). clear Hind.
assert (HFabs1 : fst (F_1294 u2 u3 u4)).
apply Res. trivial_in 4. unfold snd. unfold F_1294. unfold F_1261. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1261. unfold fst in HFabs1. unfold F_1294 in HFabs1.   
pattern u4, u2. simpl (plus _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1294 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_1309). clear Hind.
assert (HFabs1 : fst (F_1309 u2 u3 u4)).
apply Res. trivial_in 5. unfold snd. unfold F_1309. unfold F_1294. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1294. unfold fst in HFabs1. unfold F_1309 in HFabs1.   
pattern (plus u4 u2), u3. simpl (plus _ _). cbv beta.
 simpl. auto.



	(* POSITIVE DECOMPOSITION on [ 1309 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (H1 := Hind F_1234). 
assert (HFabs1 : fst (F_1234 u4 u2 u3)).
apply H1. trivial_in 0. unfold snd. unfold F_1234. unfold F_1309. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1309. unfold F_1234.

unfold fst in HFabs1. unfold F_1234 in HFabs1.

repeat (auto || (rewrite HFabs1||  auto)).


Qed.



(* the set of all formula instances from the proof *)
Definition S_1234 := fun f => exists F, In F LF_1234 /\ exists e1, exists e2, exists e3, f = F e1 e2 e3.

Theorem all_true_1234: forall F, In F LF_1234 -> forall u1: nat, forall u2: nat, forall u3: nat, fst (F u1  u2  u3).
Proof.
let n := constr:(3) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_1234);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_1234;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_1234: forall (u1: nat) (u2: nat) (u3: nat), (plus u1 (plus u2 u3)) = (plus (plus u1 u2) u3).
Proof.
do 3 intro.
apply (all_true_1234 F_1234);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
