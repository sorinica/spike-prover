
Require Import timeat_tcrt_spec.



Definition type_LF_155 :=  PLAN ->  nat ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_155 : type_LF_155:= (fun   u1 u2 _ _ _ _ => ((sortedT u1) = true -> (le (timeAt u1 u2) u2) = true, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u1):: (model_nat u2)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_187 : type_LF_155:= (fun   u7 u2 u3 u4 u5 u6 => (false = true -> (le u3 u4) = false -> (le (timeAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) u2) = true, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_169 : type_LF_155:= (fun    _ u2 _ _ _ _ => (true = true -> (le (timeAt Nil u2) u2) = true, (Term id_true nil)::(Term id_true nil)::(Term id_le ((Term id_timeAt ((Term id_Nil nil):: (model_nat u2)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_175 : type_LF_155:= (fun    _ u2 u4 u5 _ _ => (true = true -> (le (timeAt (Cons (C u4 u5) Nil) u2) u2) = true, (Term id_true nil)::(Term id_true nil)::(Term id_le ((Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_188 : type_LF_155:= (fun    _ u2 _ _ _ _ => ((le (timeAt Nil u2) u2) = true, (Term id_le ((Term id_timeAt ((Term id_Nil nil):: (model_nat u2)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_192 : type_LF_155:= (fun    _ u2 _ _ _ _ => ((le 0 u2) = true, (Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_195 : type_LF_155:= (fun    _  _ _ _ _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).
Definition F_189 : type_LF_155:= (fun    _ u2 u4 u5 _ _ => ((le (timeAt (Cons (C u4 u5) Nil) u2) u2) = true, (Term id_le ((Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_205 : type_LF_155:= (fun    _ u2 u4 u5 _ _ => ((le (time (C u4 u5)) u2) = true -> (le (time (C u4 u5)) u2) = true, (Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_209 : type_LF_155:= (fun    _ u2 u4 u5 _ _ => ((le (time (C u4 u5)) u2) = false -> (le (timeAt Nil u2) u2) = true, (Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_timeAt ((Term id_Nil nil):: (model_nat u2)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_212 : type_LF_155:= (fun    _ u2 u4 u5 _ _ => ((le (time (C u4 u5)) u2) = false -> (le 0 u2) = true, (Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_215 : type_LF_155:= (fun    _ u2 u4 _ _ _ => ((le u4 u2) = false -> (le 0 u2) = true, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_218 : type_LF_155:= (fun    _ u2 u4 _ _ _ => ((le u4 u2) = false -> true = true, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_true nil)::(Term id_true nil)::nil)).
Definition F_181 : type_LF_155:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (timeAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) u2) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_224 : type_LF_155:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (time (C u4 u5)) u2) = true -> (le (time (C u4 u5)) u2) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_228 : type_LF_155:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (time (C u4 u5)) u2) = false -> (le (timeAt (Cons (C u3 u6) u7) u2) u2) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::nil)).

Definition LF_155 := [F_155, F_187, F_169, F_175, F_188, F_192, F_195, F_189, F_205, F_209, F_212, F_215, F_218, F_181, F_224, F_228].


Function f_155 (u1: PLAN) {struct u1} : bool :=
 match u1 with
| Nil => true
| (Cons (C u4 u5) Nil) => true
| (Cons (C u4 u5) (Cons (C u3 u6) u7)) => true
end.

Lemma main_155 : forall F, In F LF_155 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, (forall F', In F' LF_155 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, less (snd (F' e1 e2 e3 e4 e5 e6)) (snd (F u1 u2 u3 u4 u5 u6)) -> fst (F' e1 e2 e3 e4 e5 e6)) -> fst (F u1 u2 u3 u4 u5 u6).
Proof.
intros F HF u1 u2 u3 u4 u5 u6; case_In HF; intro Hind.

	(* GENERATE on [ 155 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, (f_155 u1). apply f_155_ind.

(* case [ 169 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_169). clear HFabs0.
assert (HFabs0 : fst (F_169 Nil u2 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_169. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_169.
auto.


(* case [ 175 ] *)

intros _u1. intro u4. intro u5.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_175). clear HFabs0.
assert (HFabs0 : fst (F_175 Nil u2 u4 u5 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_175. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_175.
auto.



intros _u1. intro u4. intro u5. intro u3. intro u6. intro u7.  intro eq_1.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 181 ] *)

assert (Hind := HFabs0 F_181). clear HFabs0.
assert (HFabs0 : fst (F_181 u7 u2 u3 u4 u5 u6)).
apply Hind. trivial_in 13. unfold snd. unfold F_181. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_181. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 187 ] *)

assert (Hind := HFabs0 F_187). clear HFabs0.
assert (HFabs0 : fst (F_187 u7 u2 u3 u4 u5 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_187. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_187. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 187 ] *)

unfold fst. unfold F_187. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 169 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. 
assert (H := Hind F_188). 
assert (HFabs0 : fst (F_188 Nil u2 0 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_188. unfold F_169. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_169. unfold F_188.

unfold fst in HFabs0. unfold F_188 in HFabs0.
auto.



	(* NEGATIVE DECOMPOSITION on [ 175 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (H := Hind F_189). 
assert (HFabs0 : fst (F_189 Nil u2 u4 u5 0 0)).
apply H. trivial_in 7. unfold snd. unfold F_189. unfold F_175. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_175. unfold F_189.

unfold fst in HFabs0. unfold F_189 in HFabs0.
auto.



	(* REWRITING on [ 188 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. 
assert (Res := Hind F_192). clear Hind.
assert (HFabs1 : fst (F_192 Nil u2 0 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_192. unfold F_188. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_188. unfold fst in HFabs1. unfold F_192 in HFabs1.   
pattern u2. simpl (timeAt _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 192 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. 
assert (Res := Hind F_195). clear Hind.
assert (HFabs1 : fst (F_195 Nil 0 0 0 0 0)).
apply Res. trivial_in 6. unfold snd. unfold F_195. unfold F_192. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_192. unfold fst in HFabs1. unfold F_195 in HFabs1.   
pattern u2. simpl (le _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 195 ] *)

unfold fst. unfold F_195.
auto.



	(* TOTAL CASE REWRITING on [ 189 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (H: ((le (time (C u4 u5)) u2) = true) \/ ((le (time (C u4 u5)) u2) = false)). 

destruct ((le (time (C u4 u5)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 140 ] *)

assert (H1 := Hind F_205). clear Hind.
assert (HFabs0 : fst (F_205 Nil u2 u4 u5 0 0)).
apply H1. trivial_in 8. unfold snd. unfold F_205. unfold F_189. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_189. unfold F_205. unfold fst in HFabs0. unfold F_205 in HFabs0. simpl in HFabs0. 
pattern (C u4 u5).
pattern u2.
pattern Nil.
simpl (timeAt _ _). cbv beta. try unfold timeAt. try rewrite H. try rewrite H0. try unfold timeAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 141 ] *)

assert (H1 := Hind F_209). clear Hind.
assert (HFabs0 : fst (F_209 Nil u2 u4 u5 0 0)).
apply H1. trivial_in 9. unfold snd. unfold F_209. unfold F_189. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_189. unfold F_209. unfold fst in HFabs0. unfold F_209 in HFabs0. simpl in HFabs0. 
pattern (C u4 u5).
pattern u2.
pattern Nil.
simpl (timeAt _ _). cbv beta. try unfold timeAt. try rewrite H. try rewrite H0. try unfold timeAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 205 ] *)

unfold fst. unfold F_205.
auto.



	(* REWRITING on [ 209 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_212). clear Hind.
assert (HFabs1 : fst (F_212 Nil u2 u4 u5 0 0)).
apply Res. trivial_in 10. unfold snd. unfold F_212. unfold F_209. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_209. unfold fst in HFabs1. unfold F_212 in HFabs1.   
pattern u2. simpl (timeAt _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 212 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_215). clear Hind.
assert (HFabs1 : fst (F_215 Nil u2 u4 0 0 0)).
apply Res. trivial_in 11. unfold snd. unfold F_215. unfold F_212. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_212. unfold fst in HFabs1. unfold F_215 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 215 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. 
assert (Res := Hind F_218). clear Hind.
assert (HFabs1 : fst (F_218 Nil u2 u4 0 0 0)).
apply Res. trivial_in 12. unfold snd. unfold F_218. unfold F_215. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_215. unfold fst in HFabs1. unfold F_218 in HFabs1.   
pattern u2. simpl (le _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 218 ] *)

unfold fst. unfold F_218.
auto.



	(* TOTAL CASE REWRITING on [ 181 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (H: ((le (time (C u4 u5)) u2) = true) \/ ((le (time (C u4 u5)) u2) = false)). 

destruct ((le (time (C u4 u5)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 140 ] *)

assert (H1 := Hind F_224). clear Hind.
assert (HFabs0 : fst (F_224 u7 u2 u3 u4 u5 u6)).
apply H1. trivial_in 14. unfold snd. unfold F_224. unfold F_181. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_181. unfold F_224. unfold fst in HFabs0. unfold F_224 in HFabs0. simpl in HFabs0. 
pattern (C u4 u5).
pattern u2.
pattern (Cons (C u3 u6) u7).
simpl (timeAt _ _). cbv beta. try unfold timeAt. try rewrite H. try rewrite H0. try unfold timeAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 141 ] *)

assert (H1 := Hind F_228). clear Hind.
assert (HFabs0 : fst (F_228 u7 u2 u3 u4 u5 u6)).
apply H1. trivial_in 15. unfold snd. unfold F_228. unfold F_181. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_181. unfold F_228. unfold fst in HFabs0. unfold F_228 in HFabs0. simpl in HFabs0. 
pattern (C u4 u5).
pattern u2.
pattern (Cons (C u3 u6) u7).
simpl (timeAt _ _). cbv beta. try unfold timeAt. try rewrite H. try rewrite H0. try unfold timeAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 224 ] *)

unfold fst. unfold F_224.
auto.



	(* REWRITING on [ 228 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_155). clear Hind.
assert (HFabs1 : fst (F_155 (Cons (C u3 u6) u7) u2 0 0 0 0)).
apply Res. trivial_in 0. unfold snd. unfold F_155. unfold F_228. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_228. unfold fst in HFabs1. unfold F_155 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_155 := fun f => exists F, In F LF_155 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, f = F e1 e2 e3 e4 e5 e6.

Theorem all_true_155: forall F, In F LF_155 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, fst (F u1 u2  u3  u4  u5  u6).
Proof.
let n := constr:(6) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_155);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_155;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_155: forall (u1: PLAN) (u2: nat), (sortedT u1) = true -> (le (timeAt u1 u2) u2) = true.
Proof.
do 2 intro.
apply (all_true_155 F_155);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
