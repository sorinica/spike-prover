
Require Import erl_prog_spec.



Definition type_LF_157 :=  PLAN ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_157 : type_LF_157:= (fun   u1 u2 u3 _ _ => ((erl (insIn u1 u2 u3)) = u3, (Term id_erl ((Term id_insIn ((model_PLAN u1):: (model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u3)::nil)).
Definition F_169 : type_LF_157:= (fun    _ u2 u3 _ _ => ((erl (Cons (C u2 u3) Nil)) = u3, (Term id_erl ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Nil nil)::nil))::nil))::(model_nat u3)::nil)).
Definition F_175 : type_LF_157:= (fun   u6 u3 u8 u9 _ => ((le (er (C u8 u9)) u3) = true -> (erl (insIn u6 (time (C u8 u9)) u3)) = u3, (Term id_le ((Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_erl ((Term id_insIn ((model_PLAN u6):: (Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::nil))::(model_nat u3)::nil)).
Definition F_181 : type_LF_157:= (fun   u6 u2 u3 u8 u9 => ((le (er (C u8 u9)) u3) = false -> (erl (Cons (C u2 u3) (Cons (C u8 u9) u6))) = u3, (Term id_le ((Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_erl ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::(model_nat u3)::nil)).
Definition F_184 : type_LF_157:= (fun    _ u2 u3 _ _ => ((er (C u2 u3)) = u3, (Term id_er ((Term id_C ((model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u3)::nil)).
Definition F_193 : type_LF_157:= (fun    _ u3 _ _ _ => (u3 = u3, (model_nat u3)::(model_nat u3)::nil)).
Definition F_187 : type_LF_157:= (fun   u6 u3 u8 u9 _ => ((le u9 u3) = true -> (erl (insIn u6 (time (C u8 u9)) u3)) = u3, (Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_erl ((Term id_insIn ((model_PLAN u6):: (Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::nil))::(model_nat u3)::nil)).
Definition F_190 : type_LF_157:= (fun    _ u2 u3 u8 u9 => ((le (er (C u8 u9)) u3) = false -> (er (C u2 u3)) = u3, (Term id_le ((Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u3)::nil)).
Definition F_199 : type_LF_157:= (fun    _ u3 u8 u9 _ => ((le (er (C u8 u9)) u3) = false -> u3 = u3, (Term id_le ((Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u3)::nil)).

Definition LF_157 := [F_157, F_169, F_175, F_181, F_184, F_193, F_187, F_190, F_199].


Function f_157 (u1: PLAN) (u2: nat) (u3: nat) {struct u1} : PLAN :=
 match u1, u2, u3 with
| Nil, _, _ => Nil
| (Cons (C u8 u9) u6), _, _ => Nil
end.

Lemma main_157 : forall F, In F LF_157 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_157 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 157 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. 

revert Hind.

pattern u1, u2, u3, (f_157 u1 u2 u3). apply f_157_ind.

(* case [ 169 ] *)

intros _u1 _u2 _u3.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_169). clear HFabs0.
assert (HFabs0 : fst (F_169 Nil _u2 _u3 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_169. unfold F_157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_157. unfold F_169.
auto.



intros _u1 _u2 _u3. intro u8. intro u9. intro u6.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
case_eq (le (er (C u8 u9)) _u3); [intro H | intro H].

(* case [ 175 ] *)

assert (Hind := HFabs0 F_175). clear HFabs0.
assert (HFabs0 : fst (F_175 u6 _u3 u8 u9 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_175. unfold F_157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_157. unfold F_175. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 181 ] *)

assert (Hind := HFabs0 F_181). clear HFabs0.
assert (HFabs0 : fst (F_181 u6 _u2 _u3 u8 u9)).
apply Hind. trivial_in 3. unfold snd. unfold F_181. unfold F_157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_157. unfold F_181. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* REWRITING on [ 169 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_184). clear Hind.
assert (HFabs1 : fst (F_184 Nil u2 u3 0 0)).
apply Res. trivial_in 4. unfold snd. unfold F_184. unfold F_169. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_169. unfold fst in HFabs1. unfold F_184 in HFabs1.   
pattern (C u2 u3), Nil. simpl (erl _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 175 ] *)

rename u1 into _u6. rename u2 into _u3. rename u3 into _u8. rename u4 into _u9. rename u5 into d_u5. 
rename _u6 into u6. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_187). clear Hind.
assert (HFabs1 : fst (F_187 u6 u3 u8 u9 0)).
apply Res. trivial_in 6. unfold snd. unfold F_187. unfold F_175. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_175. unfold fst in HFabs1. unfold F_187 in HFabs1.   
pattern u8, u9. simpl (er _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 181 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_190). clear Hind.
assert (HFabs1 : fst (F_190 Nil u2 u3 u8 u9)).
apply Res. trivial_in 7. unfold snd. unfold F_190. unfold F_181. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_181. unfold fst in HFabs1. unfold F_190 in HFabs1.   
pattern (C u2 u3), (Cons (C u8 u9) u6). simpl (erl _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 184 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_193). clear Hind.
assert (HFabs1 : fst (F_193 Nil u3 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_193. unfold F_184. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_184. unfold fst in HFabs1. unfold F_193 in HFabs1.   
pattern u2, u3. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 193 ] *)

unfold fst. unfold F_193.
auto.



	(* REWRITING on [ 187 ] *)

rename u1 into _u6. rename u2 into _u3. rename u3 into _u8. rename u4 into _u9. rename u5 into d_u5. 
rename _u6 into u6. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_157). clear Hind.
assert (HFabs1 : fst (F_157 u6 u8 u3 0 0)).
apply Res. trivial_in 0. unfold snd. unfold F_157. unfold F_187. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_187. unfold fst in HFabs1. unfold F_157 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 190 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_199). clear Hind.
assert (HFabs1 : fst (F_199 Nil u3 u8 u9 0)).
apply Res. trivial_in 8. unfold snd. unfold F_199. unfold F_190. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_190. unfold fst in HFabs1. unfold F_199 in HFabs1.   
pattern u2, u3. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 199 ] *)

unfold fst. unfold F_199.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_157 := fun f => exists F, In F LF_157 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_157: forall F, In F LF_157 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2  u3  u4  u5).
Proof.
let n := constr:(5) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_157);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_157;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_157: forall (u1: PLAN) (u2: nat) (u3: nat), (erl (insIn u1 u2 u3)) = u3.
Proof.
do 3 intro.
apply (all_true_157 F_157);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_203 :=  PLAN ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_203 : type_LF_203:= (fun   u1 u2 u3 _ _ => ((erl (insAt u1 u2 u3)) = u3, (Term id_erl ((Term id_insAt ((model_PLAN u1):: (model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u3)::nil)).
Definition F_216 : type_LF_203:= (fun    _ u2 u3 _ _ => ((erl (Cons (C u2 u3) Nil)) = u3, (Term id_erl ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Nil nil)::nil))::nil))::(model_nat u3)::nil)).
Definition F_222 : type_LF_203:= (fun   u6 u2 u3 u8 u9 => ((le (time (C u8 u9)) u2) = true -> (erl (Cons (C u2 u3) (Cons (C u8 u9) u6))) = u3, (Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_erl ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::(model_nat u3)::nil)).
Definition F_228 : type_LF_203:= (fun   u6 u2 u3 u8 u9 => ((le (time (C u8 u9)) u2) = false -> (erl (insAt u6 u2 u3)) = u3, (Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_erl ((Term id_insAt ((model_PLAN u6):: (model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u3)::nil)).
Definition F_231 : type_LF_203:= (fun    _ u2 u3 _ _ => ((er (C u2 u3)) = u3, (Term id_er ((Term id_C ((model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u3)::nil)).
Definition F_240 : type_LF_203:= (fun    _ u3 _ _ _ => (u3 = u3, (model_nat u3)::(model_nat u3)::nil)).
Definition F_234 : type_LF_203:= (fun    _ u2 u3 u8 u9 => ((le (time (C u8 u9)) u2) = true -> (er (C u2 u3)) = u3, (Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u3)::nil)).
Definition F_243 : type_LF_203:= (fun    _ u2 u3 u8 _ => ((le u8 u2) = true -> (er (C u2 u3)) = u3, (Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u3)::nil)).
Definition F_246 : type_LF_203:= (fun    _ u2 u3 u8 _ => ((le u8 u2) = true -> u3 = u3, (Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u3)::nil)).

Definition LF_203 := [F_203, F_216, F_222, F_228, F_231, F_240, F_234, F_243, F_246].


Function f_203 (u1: PLAN) (u2: nat) (u3: nat) {struct u1} : PLAN :=
 match u1, u2, u3 with
| Nil, _, _ => Nil
| (Cons (C u8 u9) u6), _, _ => Nil
end.

Lemma main_203 : forall F, In F LF_203 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_203 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 203 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. 

revert Hind.

pattern u1, u2, u3, (f_203 u1 u2 u3). apply f_203_ind.

(* case [ 216 ] *)

intros _u1 _u2 _u3.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_216). clear HFabs0.
assert (HFabs0 : fst (F_216 Nil _u2 _u3 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_216. unfold F_203. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_203. unfold F_216.
auto.



intros _u1 _u2 _u3. intro u8. intro u9. intro u6.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
case_eq (le (time (C u8 u9)) _u2); [intro H | intro H].

(* case [ 222 ] *)

assert (Hind := HFabs0 F_222). clear HFabs0.
assert (HFabs0 : fst (F_222 u6 _u2 _u3 u8 u9)).
apply Hind. trivial_in 2. unfold snd. unfold F_222. unfold F_203. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_203. unfold F_222. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 228 ] *)

assert (Hind := HFabs0 F_228). clear HFabs0.
assert (HFabs0 : fst (F_228 u6 _u2 _u3 u8 u9)).
apply Hind. trivial_in 3. unfold snd. unfold F_228. unfold F_203. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_203. unfold F_228. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* REWRITING on [ 216 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_231). clear Hind.
assert (HFabs1 : fst (F_231 Nil u2 u3 0 0)).
apply Res. trivial_in 4. unfold snd. unfold F_231. unfold F_216. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_216. unfold fst in HFabs1. unfold F_231 in HFabs1.   
pattern (C u2 u3), Nil. simpl (erl _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 222 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_234). clear Hind.
assert (HFabs1 : fst (F_234 Nil u2 u3 u8 u9)).
apply Res. trivial_in 6. unfold snd. unfold F_234. unfold F_222. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_222. unfold fst in HFabs1. unfold F_234 in HFabs1.   
pattern (C u2 u3), (Cons (C u8 u9) u6). simpl (erl _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 228 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_203). clear Hind.
assert (HFabs1 : fst (F_203 u6 u2 u3 0 0)).
apply Res. trivial_in 0. unfold snd. unfold F_203. unfold F_228. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_228. unfold fst in HFabs1. unfold F_203 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 231 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_240). clear Hind.
assert (HFabs1 : fst (F_240 Nil u3 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_240. unfold F_231. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_231. unfold fst in HFabs1. unfold F_240 in HFabs1.   
pattern u2, u3. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 240 ] *)

unfold fst. unfold F_240.
auto.



	(* REWRITING on [ 234 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_243). clear Hind.
assert (HFabs1 : fst (F_243 Nil u2 u3 u8 0)).
apply Res. trivial_in 7. unfold snd. unfold F_243. unfold F_234. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_234. unfold fst in HFabs1. unfold F_243 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 243 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into d_u5. 
rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. 
assert (Res := Hind F_246). clear Hind.
assert (HFabs1 : fst (F_246 Nil u2 u3 u8 0)).
apply Res. trivial_in 8. unfold snd. unfold F_246. unfold F_243. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_243. unfold fst in HFabs1. unfold F_246 in HFabs1.   
pattern u2, u3. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 246 ] *)

unfold fst. unfold F_246.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_203 := fun f => exists F, In F LF_203 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_203: forall F, In F LF_203 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2  u3  u4  u5).
Proof.
let n := constr:(5) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_203);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_203;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_203: forall (u1: PLAN) (u2: nat) (u3: nat), (erl (insAt u1 u2 u3)) = u3.
Proof.
do 3 intro.
apply (all_true_203 F_203);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_251 :=  PLAN ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_251 : type_LF_251:= (fun   u1 u2 u3 _ _ => ((erl (prog u1 u2 u3)) = (erl u1), (Term id_erl ((Term id_prog ((model_PLAN u1):: (model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_erl ((model_PLAN u1)::nil))::nil)).
Definition F_265 : type_LF_251:= (fun    _  _ _ _ _ => ((erl Nil) = (erl Nil), (Term id_erl ((Term id_Nil nil)::nil))::(Term id_erl ((Term id_Nil nil)::nil))::nil)).
Definition F_271 : type_LF_251:= (fun   u4 u2 u3 u8 u9 => ((le (progAt (prog u4 u2 u3) (plus (time (C u8 u9)) u3)) (er (C u8 u9))) = true -> (erl (insAt (prog u4 u2 u3) (plus (time (C u8 u9)) u3) (er (C u8 u9)))) = (erl (Cons (C u8 u9) u4)), (Term id_le ((Term id_progAt ((Term id_prog ((model_PLAN u4):: (model_nat u2):: (model_nat u3)::nil)):: (Term id_plus ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::nil)):: (Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::nil))::(Term id_true nil)::(Term id_erl ((Term id_insAt ((Term id_prog ((model_PLAN u4):: (model_nat u2):: (model_nat u3)::nil)):: (Term id_plus ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil)):: (Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::nil))::nil))::(Term id_erl ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u4)::nil))::nil))::nil)).
Definition F_277 : type_LF_251:= (fun   u4 u2 u3 u8 u9 => ((le (progAt (prog u4 u2 u3) (plus (time (C u8 u9)) u3)) (er (C u8 u9))) = false -> (erl (insIn (prog u4 u2 u3) (plus (time (C u8 u9)) u2) (er (C u8 u9)))) = (erl (Cons (C u8 u9) u4)), (Term id_le ((Term id_progAt ((Term id_prog ((model_PLAN u4):: (model_nat u2):: (model_nat u3)::nil)):: (Term id_plus ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::nil)):: (Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::nil))::(Term id_false nil)::(Term id_erl ((Term id_insIn ((Term id_prog ((model_PLAN u4):: (model_nat u2):: (model_nat u3)::nil)):: (Term id_plus ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil)):: (Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::nil))::nil))::(Term id_erl ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u4)::nil))::nil))::nil)).
Definition F_280 : type_LF_251:= (fun   u4 u2 u3 u8 u9 => ((le (progAt (prog u4 u2 u3) (plus (time (C u8 u9)) u3)) (er (C u8 u9))) = true -> (er (C u8 u9)) = (erl (Cons (C u8 u9) u4)), (Term id_le ((Term id_progAt ((Term id_prog ((model_PLAN u4):: (model_nat u2):: (model_nat u3)::nil)):: (Term id_plus ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::nil)):: (Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::(Term id_erl ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u4)::nil))::nil))::nil)).
Definition F_286 : type_LF_251:= (fun   u4 u2 u3 u8 u9 => ((le (progAt (prog u4 u2 u3) (plus (time (C u8 u9)) u3)) (er (C u8 u9))) = true -> (er (C u8 u9)) = (er (C u8 u9)), (Term id_le ((Term id_progAt ((Term id_prog ((model_PLAN u4):: (model_nat u2):: (model_nat u3)::nil)):: (Term id_plus ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::nil)):: (Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::(Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::nil)).
Definition F_283 : type_LF_251:= (fun   u4 u2 u3 u8 u9 => ((le (progAt (prog u4 u2 u3) (plus (time (C u8 u9)) u3)) (er (C u8 u9))) = false -> (er (C u8 u9)) = (erl (Cons (C u8 u9) u4)), (Term id_le ((Term id_progAt ((Term id_prog ((model_PLAN u4):: (model_nat u2):: (model_nat u3)::nil)):: (Term id_plus ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::nil)):: (Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::nil))::(Term id_false nil)::(Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::(Term id_erl ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u4)::nil))::nil))::nil)).
Definition F_289 : type_LF_251:= (fun   u4 u2 u3 u8 u9 => ((le (progAt (prog u4 u2 u3) (plus (time (C u8 u9)) u3)) (er (C u8 u9))) = false -> (er (C u8 u9)) = (er (C u8 u9)), (Term id_le ((Term id_progAt ((Term id_prog ((model_PLAN u4):: (model_nat u2):: (model_nat u3)::nil)):: (Term id_plus ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::nil)):: (Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::nil))::(Term id_false nil)::(Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::(Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::nil)).

Definition LF_251 := [F_251, F_265, F_271, F_277, F_280, F_286, F_283, F_289].


Function f_251 (u1: PLAN) (u2: nat) (u3: nat) {struct u1} : PLAN :=
 match u1, u2, u3 with
| Nil, _, _ => Nil
| (Cons (C u8 u9) u4), _, _ => Nil
end.

Lemma main_251 : forall F, In F LF_251 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_251 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 251 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. 

revert Hind.

pattern u1, u2, u3, (f_251 u1 u2 u3). apply f_251_ind.

(* case [ 265 ] *)

intros _u1 _u2 _u3.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_265). clear HFabs0.
assert (HFabs0 : fst (F_265 Nil 0 0 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_265. unfold F_251. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_251. unfold F_265.
auto.



intros _u1 _u2 _u3. intro u8. intro u9. intro u4.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
case_eq (le (progAt (prog u4 _u2 _u3) (plus (time (C u8 u9)) _u3)) (er (C u8 u9))); [intro H | intro H].

(* case [ 271 ] *)

assert (Hind := HFabs0 F_271). clear HFabs0.
assert (HFabs0 : fst (F_271 u4 _u2 _u3 u8 u9)).
apply Hind. trivial_in 2. unfold snd. unfold F_271. unfold F_251. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_251. unfold F_271. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 277 ] *)

assert (Hind := HFabs0 F_277). clear HFabs0.
assert (HFabs0 : fst (F_277 u4 _u2 _u3 u8 u9)).
apply Hind. trivial_in 3. unfold snd. unfold F_277. unfold F_251. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_251. unfold F_277. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* TAUTOLOGY on [ 265 ] *)

unfold fst. unfold F_265.
auto.



	(* REWRITING on [ 271 ] *)

rename u1 into _u4. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u4 into u4. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_280). clear Hind.
assert (HFabs1 : fst (F_280 u4 u2 u3 u8 u9)).
apply Res. trivial_in 4. unfold snd. unfold F_280. unfold F_271. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_271. unfold fst in HFabs1. unfold F_280 in HFabs1.  specialize true_203 with (u1 := (prog u4 u2 u3)) (u2 := (plus (time (C u8 u9)) u3)) (u3 := (er (C u8 u9))). intro L. try rewrite L.
  simpl. auto.



	(* REWRITING on [ 277 ] *)

rename u1 into _u4. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u4 into u4. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_283). clear Hind.
assert (HFabs1 : fst (F_283 u4 u2 u3 u8 u9)).
apply Res. trivial_in 6. unfold snd. unfold F_283. unfold F_277. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_277. unfold fst in HFabs1. unfold F_283 in HFabs1.  specialize true_157 with (u1 := (prog u4 u2 u3)) (u2 := (plus (time (C u8 u9)) u2)) (u3 := (er (C u8 u9))). intro L. try rewrite L.
  simpl. auto.



	(* REWRITING on [ 280 ] *)

rename u1 into _u4. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u4 into u4. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_286). clear Hind.
assert (HFabs1 : fst (F_286 u4 u2 u3 u8 u9)).
apply Res. trivial_in 5. unfold snd. unfold F_286. unfold F_280. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_280. unfold fst in HFabs1. unfold F_286 in HFabs1.   
pattern (C u8 u9), u4. simpl (erl _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 286 ] *)

unfold fst. unfold F_286.
auto.



	(* REWRITING on [ 283 ] *)

rename u1 into _u4. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u4 into u4. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_289). clear Hind.
assert (HFabs1 : fst (F_289 u4 u2 u3 u8 u9)).
apply Res. trivial_in 7. unfold snd. unfold F_289. unfold F_283. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_283. unfold fst in HFabs1. unfold F_289 in HFabs1.   
pattern (C u8 u9), u4. simpl (erl _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 289 ] *)

unfold fst. unfold F_289.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_251 := fun f => exists F, In F LF_251 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_251: forall F, In F LF_251 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2  u3  u4  u5).
Proof.
let n := constr:(5) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_251);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_251;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_251: forall (u1: PLAN) (u2: nat) (u3: nat), (erl (prog u1 u2 u3)) = (erl u1).
Proof.
do 3 intro.
apply (all_true_251 F_251);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
