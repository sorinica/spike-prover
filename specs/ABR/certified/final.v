
Require Import final_spec.



Definition type_LF_158 :=  nat ->  nat -> (Prop * (List.list term)).

Definition F_158 : type_LF_158:= (fun    u1 u2 => ((le u1 u2) = false -> (le u1 u2) = true -> False, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_173 : type_LF_158:= (fun    u2 _ => (true = false -> (le 0 u2) = true -> False, (Term id_true nil)::(Term id_false nil)::(Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_179 : type_LF_158:= (fun    u3 _ => (false = false -> (le (S u3) 0) = true -> False, (Term id_false nil)::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_185 : type_LF_158:= (fun    u3 u4 => ((le u3 u4) = false -> (le (S u3) (S u4)) = true -> False, (Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_S ((model_nat u4)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_186 : type_LF_158:= (fun    u3 _ => ((le (S u3) 0) = true -> False, (Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_192 : type_LF_158:= (fun     _ _ => (false = true -> False, (Term id_false nil)::(Term id_true nil)::nil)).

Definition LF_158 := [F_158, F_173, F_179, F_185, F_186, F_192].


Function f_158 (u1: nat) (u2: nat) {struct u1} : bool :=
 match u1, u2 with
| 0, _ => true
| (S u3), 0 => true
| (S u3), (S u4) => true
end.

Lemma main_158 : forall F, In F LF_158 -> forall u1, forall u2, (forall F', In F' LF_158 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 158 ] *)

rename u1 into _u1. rename u2 into _u2. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_158 u1 u2). apply f_158_ind.

(* case [ 173 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_173). clear HFabs0.
assert (HFabs0 : fst (F_173 _u2 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_173. unfold F_158. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_158. unfold F_173.
auto.


(* case [ 179 ] *)

intros _u1 _u2. intro u3.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_179). clear HFabs0.
assert (HFabs0 : fst (F_179 u3 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_179. unfold F_158. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_158. unfold F_179.
auto.


(* case [ 185 ] *)

intros _u1 _u2. intro u3.  intro eq_1. intro u4.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_185). clear HFabs0.
assert (HFabs0 : fst (F_185 u3 u4)).
apply Hind. trivial_in 3. unfold snd. unfold F_185. unfold F_158. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_158. unfold F_185.
auto.





	(* NEGATIVE CLASH on [ 173 ] *)

unfold fst. unfold F_173. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 179 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (H := Hind F_186). 
assert (HFabs0 : fst (F_186 u3 0)).
apply H. trivial_in 4. unfold snd. unfold F_186. unfold F_179. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_179. unfold F_186.

unfold fst in HFabs0. unfold F_186 in HFabs0.
auto.



	(* REWRITING on [ 185 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_158). clear Hind.
assert (HFabs1 : fst (F_158 u3 u4)).
apply Res. trivial_in 0. unfold snd. unfold F_158. unfold F_185. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_185. unfold fst in HFabs1. unfold F_158 in HFabs1.   
pattern u3, u4. simpl (le _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 186 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (Res := Hind F_192). clear Hind.
assert (HFabs1 : fst (F_192 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_192. unfold F_186. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_186. unfold fst in HFabs1. unfold F_192 in HFabs1.   
pattern u3. simpl (le _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE CLASH on [ 192 ] *)

unfold fst. unfold F_192. intros. try discriminate.



Qed.



(* the set of all formula instances from the proof *)
Definition S_158 := fun f => exists F, In F LF_158 /\ exists e1, exists e2, f = F e1 e2.

Theorem all_true_158: forall F, In F LF_158 -> forall u1: nat, forall u2: nat, fst (F u1  u2).
Proof.
let n := constr:(2) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_158);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_158;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_158: forall (u1: nat) (u2: nat), (le u1 u2) = false -> (le u1 u2) = true -> False.
Proof.
do 2 intro.
apply (all_true_158 F_158);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_196 :=  PLAN ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_196 : type_LF_196:= (fun   u1  _ _ _ _ => ((sortedT u1) = true -> (sortedT u1) = false -> False, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u1)::nil))::(Term id_false nil)::nil)).
Definition F_229 : type_LF_196:= (fun   u6 u2 u3 u4 u5 => (false = true -> (sortedT (Cons (C u3 u4) (Cons (C u2 u5) u6))) = false -> (le u2 u3) = false -> False, (Term id_false nil)::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::(Term id_false nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::nil)).
Definition F_211 : type_LF_196:= (fun    _  _ _ _ _ => (true = true -> (sortedT Nil) = false -> False, (Term id_true nil)::(Term id_true nil)::(Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_false nil)::nil)).
Definition F_217 : type_LF_196:= (fun    _ u3 u4 _ _ => (true = true -> (sortedT (Cons (C u3 u4) Nil)) = false -> False, (Term id_true nil)::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_false nil)::nil)).
Definition F_230 : type_LF_196:= (fun    _  _ _ _ _ => ((sortedT Nil) = false -> False, (Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_false nil)::nil)).
Definition F_234 : type_LF_196:= (fun    _  _ _ _ _ => (true = false -> False, (Term id_true nil)::(Term id_false nil)::nil)).
Definition F_231 : type_LF_196:= (fun    _ u3 u4 _ _ => ((sortedT (Cons (C u3 u4) Nil)) = false -> False, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_false nil)::nil)).
Definition F_237 : type_LF_196:= (fun    _  _ _ _ _ => (true = false -> False, (Term id_true nil)::(Term id_false nil)::nil)).
Definition F_223 : type_LF_196:= (fun   u6 u2 u3 u4 u5 => ((sortedT (Cons (C u2 u5) u6)) = true -> (sortedT (Cons (C u3 u4) (Cons (C u2 u5) u6))) = false -> (le u2 u3) = true -> False, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::(Term id_false nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::nil)).
Definition F_249 : type_LF_196:= (fun   u6 u2 u3 u5 _ => ((sortedT (Cons (C u2 u5) u6)) = true -> false = false -> (le u2 u3) = true -> (le u2 u3) = false -> False, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_false nil)::(Term id_false nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::nil)).
Definition F_250 : type_LF_196:= (fun   u6 u2 u3 u5 _ => ((sortedT (Cons (C u2 u5) u6)) = true -> (le u2 u3) = true -> (le u2 u3) = false -> False, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::nil)).

Definition LF_196 := [F_196, F_229, F_211, F_217, F_230, F_234, F_231, F_237, F_223, F_249, F_250].


Function f_196 (u1: PLAN) {struct u1} : bool :=
 match u1 with
| Nil => true
| (Cons (C u3 u4) Nil) => true
| (Cons (C u3 u4) (Cons (C u2 u5) u6)) => true
end.

Lemma main_196 : forall F, In F LF_196 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_196 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 196 ] *)

rename u1 into _u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_196 u1). apply f_196_ind.

(* case [ 211 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_211). clear HFabs0.
assert (HFabs0 : fst (F_211 Nil 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_211. unfold F_196. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_196. unfold F_211.
auto.


(* case [ 217 ] *)

intros _u1. intro u3. intro u4.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_217). clear HFabs0.
assert (HFabs0 : fst (F_217 Nil u3 u4 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_217. unfold F_196. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_196. unfold F_217.
auto.



intros _u1. intro u3. intro u4. intro u2. intro u5. intro u6.  intro eq_1.  intro HFabs0.
case_eq (le u2 u3); [intro H | intro H].

(* case [ 223 ] *)

assert (Hind := HFabs0 F_223). clear HFabs0.
assert (HFabs0 : fst (F_223 u6 u2 u3 u4 u5)).
apply Hind. trivial_in 8. unfold snd. unfold F_223. unfold F_196. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_196. unfold F_223. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 229 ] *)

assert (Hind := HFabs0 F_229). clear HFabs0.
assert (HFabs0 : fst (F_229 u6 u2 u3 u4 u5)).
apply Hind. trivial_in 1. unfold snd. unfold F_229. unfold F_196. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_196. unfold F_229. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 229 ] *)

unfold fst. unfold F_229. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 211 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (H := Hind F_230). 
assert (HFabs0 : fst (F_230 Nil 0 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_230. unfold F_211. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_211. unfold F_230.

unfold fst in HFabs0. unfold F_230 in HFabs0.
auto.



	(* NEGATIVE DECOMPOSITION on [ 217 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
assert (H := Hind F_231). 
assert (HFabs0 : fst (F_231 Nil u3 u4 0 0)).
apply H. trivial_in 6. unfold snd. unfold F_231. unfold F_217. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_217. unfold F_231.

unfold fst in HFabs0. unfold F_231 in HFabs0.
auto.



	(* REWRITING on [ 230 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (Res := Hind F_234). clear Hind.
assert (HFabs1 : fst (F_234 Nil 0 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_234. unfold F_230. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_230. unfold fst in HFabs1. unfold F_234 in HFabs1.    simpl. auto.



	(* NEGATIVE CLASH on [ 234 ] *)

unfold fst. unfold F_234. intros. try discriminate.



	(* REWRITING on [ 231 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_237). clear Hind.
assert (HFabs1 : fst (F_237 Nil 0 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_237. unfold F_231. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_231. unfold fst in HFabs1. unfold F_237 in HFabs1.   
pattern (C u3 u4). simpl (sortedT _). cbv beta.
 simpl. auto.



	(* NEGATIVE CLASH on [ 237 ] *)

unfold fst. unfold F_237. intros. try discriminate.



	(* TOTAL CASE REWRITING on [ 223 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. 
assert (H: ((le u2 u3) = true) \/ ((le u2 u3) = false)). 

destruct ((le u2 u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 109 ] *)

assert (H1 := Hind F_196). clear Hind.
assert (HFabs0 : fst (F_196 (Cons (C u2 u5) u6) 0 0 0 0)).
apply H1. trivial_in 0. unfold snd. unfold F_196. unfold F_223. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_223. unfold F_196. unfold fst in HFabs0. unfold F_196 in HFabs0. simpl in HFabs0. 
pattern u2.
pattern u3.
pattern u4.
pattern u5.
pattern u6.
simpl (sortedT _). cbv beta. try unfold sortedT. try rewrite H. try rewrite H0. try unfold sortedT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 110 ] *)

assert (H1 := Hind F_249). clear Hind.
assert (HFabs0 : fst (F_249 u6 u2 u3 u5 0)).
apply H1. trivial_in 9. unfold snd. unfold F_249. unfold F_223. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_223. unfold F_249. unfold fst in HFabs0. unfold F_249 in HFabs0. simpl in HFabs0. 
pattern u2.
pattern u3.
pattern u4.
pattern u5.
pattern u6.
simpl (sortedT _). cbv beta. try unfold sortedT. try rewrite H. try rewrite H0. try unfold sortedT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE DECOMPOSITION on [ 249 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into d_u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
assert (H := Hind F_250). 
assert (HFabs0 : fst (F_250 u6 u2 u3 u5 0)).
apply H. trivial_in 10. unfold snd. unfold F_250. unfold F_249. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_249. unfold F_250.

unfold fst in HFabs0. unfold F_250 in HFabs0.
auto.



	(* SUBSUMPTION on [ 250 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into d_u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
unfold fst. unfold F_250. specialize true_158 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_196 := fun f => exists F, In F LF_196 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_196: forall F, In F LF_196 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2  u3  u4  u5).
Proof.
let n := constr:(5) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_196);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_196;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_196: forall (u1: PLAN), (sortedT u1) = true -> (sortedT u1) = false -> False.
Proof.
do 1 intro.
apply (all_true_196 F_196);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_257 :=  nat ->  nat ->  nat ->  PLAN -> (Prop * (List.list term)).

Definition F_257 : type_LF_257:= (fun   u2 u3 u4 u1 => ((acr u1 u2 u3 u4) = (acr1 u1 u2 u3 u4), (Term id_acr ((model_PLAN u1):: (model_nat u2):: (model_nat u3):: (model_nat u4)::nil))::(Term id_acr1 ((model_PLAN u1):: (model_nat u2):: (model_nat u3):: (model_nat u4)::nil))::nil)).
Definition F_267 : type_LF_257:= (fun   u2 u3 u4 u1 => ((sortedT u1) = true -> (le u3 u4) = false -> (acr u1 u2 u3 u4) = (progAt (prog u1 u3 u4) u2), (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_acr ((model_PLAN u1):: (model_nat u2):: (model_nat u3):: (model_nat u4)::nil))::(Term id_progAt ((Term id_prog ((model_PLAN u1):: (model_nat u3):: (model_nat u4)::nil)):: (model_nat u2)::nil))::nil)).
Definition F_294 : type_LF_257:= (fun   u2 u3 u4 u1 => ((sortedT u1) = true -> (le u3 u4) = false -> (sortedT u1) = true -> (le u3 u4) = false -> (maxEr (wind u1 u2 u3 u4)) = (progAt (prog u1 u3 u4) u2), (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_maxEr ((Term id_wind ((model_PLAN u1):: (model_nat u2):: (model_nat u3):: (model_nat u4)::nil))::nil))::(Term id_progAt ((Term id_prog ((model_PLAN u1):: (model_nat u3):: (model_nat u4)::nil)):: (model_nat u2)::nil))::nil)).
Definition F_298 : type_LF_257:= (fun   u2 u3 u4 u1 => ((sortedT u1) = true -> (le u3 u4) = false -> (sortedT u1) = false -> 0 = (progAt (prog u1 u3 u4) u2), (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u1)::nil))::(Term id_false nil)::(Term id_0 nil)::(Term id_progAt ((Term id_prog ((model_PLAN u1):: (model_nat u3):: (model_nat u4)::nil)):: (model_nat u2)::nil))::nil)).
Definition F_302 : type_LF_257:= (fun   u2 u3 u4 u1 => ((sortedT u1) = true -> (le u3 u4) = false -> (sortedT u1) = true -> (le u3 u4) = true -> 0 = (progAt (prog u1 u3 u4) u2), (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_0 nil)::(Term id_progAt ((Term id_prog ((model_PLAN u1):: (model_nat u3):: (model_nat u4)::nil)):: (model_nat u2)::nil))::nil)).
Definition F_271 : type_LF_257:= (fun   u2 u3 u4 u1 => ((sortedT u1) = false -> (acr u1 u2 u3 u4) = 0, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_false nil)::(Term id_acr ((model_PLAN u1):: (model_nat u2):: (model_nat u3):: (model_nat u4)::nil))::(Term id_0 nil)::nil)).
Definition F_322 : type_LF_257:= (fun    _ _ _ u1 => ((sortedT u1) = false -> (sortedT u1) = false -> 0 = 0, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u1)::nil))::(Term id_false nil)::(Term id_0 nil)::(Term id_0 nil)::nil)).
Definition F_326 : type_LF_257:= (fun   u3 u4 _ u1 => ((sortedT u1) = false -> (sortedT u1) = true -> (le u3 u4) = true -> 0 = 0, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_0 nil)::(Term id_0 nil)::nil)).
Definition F_318 : type_LF_257:= (fun   u2 u3 u4 u1 => ((sortedT u1) = false -> (sortedT u1) = true -> (le u3 u4) = false -> (maxEr (wind u1 u2 u3 u4)) = 0, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_maxEr ((Term id_wind ((model_PLAN u1):: (model_nat u2):: (model_nat u3):: (model_nat u4)::nil))::nil))::(Term id_0 nil)::nil)).
Definition F_275 : type_LF_257:= (fun   u2 u3 u4 u1 => ((sortedT u1) = true -> (le u3 u4) = true -> (acr u1 u2 u3 u4) = 0, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_acr ((model_PLAN u1):: (model_nat u2):: (model_nat u3):: (model_nat u4)::nil))::(Term id_0 nil)::nil)).
Definition F_340 : type_LF_257:= (fun   u3 u4 _ u1 => ((sortedT u1) = true -> (le u3 u4) = true -> (sortedT u1) = false -> 0 = 0, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u1)::nil))::(Term id_false nil)::(Term id_0 nil)::(Term id_0 nil)::nil)).
Definition F_344 : type_LF_257:= (fun   u3 u4 _ u1 => ((sortedT u1) = true -> (le u3 u4) = true -> (sortedT u1) = true -> (le u3 u4) = true -> 0 = 0, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_0 nil)::(Term id_0 nil)::nil)).
Definition F_336 : type_LF_257:= (fun   u2 u3 u4 u1 => ((sortedT u1) = true -> (le u3 u4) = true -> (sortedT u1) = true -> (le u3 u4) = false -> (maxEr (wind u1 u2 u3 u4)) = 0, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_maxEr ((Term id_wind ((model_PLAN u1):: (model_nat u2):: (model_nat u3):: (model_nat u4)::nil))::nil))::(Term id_0 nil)::nil)).

Definition LF_257 := [F_257, F_267, F_294, F_298, F_302, F_271, F_322, F_326, F_318, F_275, F_340, F_344, F_336].



Hypothesis true_156: forall u1 u2 u3 u4, (sortedT u1) = true -> (le u2 u3) = false -> (progAt (prog u1 u2 u3) u4) = (maxEr (wind u1 u4 u2 u3)).

Lemma main_257 : forall F, In F LF_257 -> forall u1, forall u2, forall u3, forall u4, (forall F', In F' LF_257 -> forall e1, forall e2, forall e3, forall e4, less (snd (F' e1 e2 e3 e4)) (snd (F u1 u2 u3 u4)) -> fst (F' e1 e2 e3 e4)) -> fst (F u1 u2 u3 u4).
Proof.
intros F HF u1 u2 u3 u4; case_In HF; intro Hind.

	(* TOTAL CASE REWRITING on [ 257 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. rename u4 into _u1. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u1 into u1. 
assert (H: ((sortedT u1) = true) /\ ((le u3 u4) = false) \/ ((sortedT u1) = false) \/ ((sortedT u1) = true) /\ ((le u3 u4) = true)). 

destruct ((le u3 u4)); destruct ((sortedT u1)); auto.

destruct H as [[H H0]|[H|[H H0]]].

(* rewriting with the axiom [ 151 ] *)

assert (H1 := Hind F_267). clear Hind.
assert (HFabs0 : fst (F_267 u2 u3 u4 u1)).
apply H1. trivial_in 1. unfold snd. unfold F_267. unfold F_257. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_257. unfold F_267. unfold fst in HFabs0. unfold F_267 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern u2.
simpl (acr1 _ _ _ _). cbv beta. try unfold acr1. try rewrite H. try rewrite H0. try unfold acr1 in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 152 ] *)

assert (H1 := Hind F_271). clear Hind.
assert (HFabs0 : fst (F_271 u2 u3 u4 u1)).
apply H1. trivial_in 5. unfold snd. unfold F_271. unfold F_257. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_257. unfold F_271. unfold fst in HFabs0. unfold F_271 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u2.
pattern u3.
pattern u4.
simpl (acr1 _ _ _ _). cbv beta. try unfold acr1. try rewrite H. try rewrite H0. try unfold acr1 in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 153 ] *)

assert (H1 := Hind F_275). clear Hind.
assert (HFabs0 : fst (F_275 u2 u3 u4 u1)).
apply H1. trivial_in 9. unfold snd. unfold F_275. unfold F_257. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_257. unfold F_275. unfold fst in HFabs0. unfold F_275 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern u2.
simpl (acr1 _ _ _ _). cbv beta. try unfold acr1. try rewrite H. try rewrite H0. try unfold acr1 in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TOTAL CASE REWRITING on [ 267 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. rename u4 into _u1. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u1 into u1. 
assert (H: ((sortedT u1) = true) /\ ((le u3 u4) = false) \/ ((sortedT u1) = false) \/ ((sortedT u1) = true) /\ ((le u3 u4) = true)). 

destruct ((le u3 u4)); destruct ((sortedT u1)); auto.

destruct H as [[H H0]|[H|[H H0]]].

(* rewriting with the axiom [ 125 ] *)

assert (H1 := Hind F_294). clear Hind.
assert (HFabs0 : fst (F_294 u2 u3 u4 u1)).
apply H1. trivial_in 2. unfold snd. unfold F_294. unfold F_267. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_267. unfold F_294. unfold fst in HFabs0. unfold F_294 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern u2.
simpl (acr _ _ _ _). cbv beta. try unfold acr. try rewrite H. try rewrite H0. try unfold acr in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 126 ] *)

assert (H1 := Hind F_298). clear Hind.
assert (HFabs0 : fst (F_298 u2 u3 u4 u1)).
apply H1. trivial_in 3. unfold snd. unfold F_298. unfold F_267. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_267. unfold F_298. unfold fst in HFabs0. unfold F_298 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u2.
pattern u3.
pattern u4.
simpl (acr _ _ _ _). cbv beta. try unfold acr. try rewrite H. try rewrite H0. try unfold acr in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 127 ] *)

assert (H1 := Hind F_302). clear Hind.
assert (HFabs0 : fst (F_302 u2 u3 u4 u1)).
apply H1. trivial_in 4. unfold snd. unfold F_302. unfold F_267. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_267. unfold F_302. unfold fst in HFabs0. unfold F_302 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern u2.
simpl (acr _ _ _ _). cbv beta. try unfold acr. try rewrite H. try rewrite H0. try unfold acr in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* SUBSUMPTION on [ 294 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. rename u4 into _u1. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u1 into u1. 
unfold fst. unfold F_294. specialize true_156 with (u1 := u1) (u2 := u3) (u3 := u4) (u4 := u2).
(auto || symmetry; auto).



	(* SUBSUMPTION on [ 298 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. rename u4 into _u1. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u1 into u1. 
unfold fst. unfold F_298. specialize true_196 with (u1 := u1). intro L. intros. contradict L. (auto || symmetry; auto).



	(* SUBSUMPTION on [ 302 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. rename u4 into _u1. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u1 into u1. 
unfold fst. unfold F_302. specialize true_158 with (u1 := u3) (u2 := u4). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 271 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. rename u4 into _u1. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u1 into u1. 
assert (H: ((sortedT u1) = true) /\ ((le u3 u4) = false) \/ ((sortedT u1) = false) \/ ((sortedT u1) = true) /\ ((le u3 u4) = true)). 

destruct ((le u3 u4)); destruct ((sortedT u1)); auto.

destruct H as [[H H0]|[H|[H H0]]].

(* rewriting with the axiom [ 125 ] *)

assert (H1 := Hind F_318). clear Hind.
assert (HFabs0 : fst (F_318 u2 u3 u4 u1)).
apply H1. trivial_in 8. unfold snd. unfold F_318. unfold F_271. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_271. unfold F_318. unfold fst in HFabs0. unfold F_318 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern u2.
simpl (acr _ _ _ _). cbv beta. try unfold acr. try rewrite H. try rewrite H0. try unfold acr in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 126 ] *)

assert (H1 := Hind F_322). clear Hind.
assert (HFabs0 : fst (F_322 0 0 0 u1)).
apply H1. trivial_in 6. unfold snd. unfold F_322. unfold F_271. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_271. unfold F_322. unfold fst in HFabs0. unfold F_322 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u2.
pattern u3.
pattern u4.
simpl (acr _ _ _ _). cbv beta. try unfold acr. try rewrite H. try rewrite H0. try unfold acr in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 127 ] *)

assert (H1 := Hind F_326). clear Hind.
assert (HFabs0 : fst (F_326 u3 u4 0 u1)).
apply H1. trivial_in 7. unfold snd. unfold F_326. unfold F_271. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_271. unfold F_326. unfold fst in HFabs0. unfold F_326 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern u2.
simpl (acr _ _ _ _). cbv beta. try unfold acr. try rewrite H. try rewrite H0. try unfold acr in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 322 ] *)

unfold fst. unfold F_322.
auto.



	(* TAUTOLOGY on [ 326 ] *)

unfold fst. unfold F_326.
auto.



	(* SUBSUMPTION on [ 318 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. rename u4 into _u1. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u1 into u1. 
unfold fst. unfold F_318. specialize true_196 with (u1 := u1). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 275 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. rename u4 into _u1. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u1 into u1. 
assert (H: ((sortedT u1) = true) /\ ((le u3 u4) = false) \/ ((sortedT u1) = false) \/ ((sortedT u1) = true) /\ ((le u3 u4) = true)). 

destruct ((le u3 u4)); destruct ((sortedT u1)); auto.

destruct H as [[H H0]|[H|[H H0]]].

(* rewriting with the axiom [ 125 ] *)

assert (H1 := Hind F_336). clear Hind.
assert (HFabs0 : fst (F_336 u2 u3 u4 u1)).
apply H1. trivial_in 12. unfold snd. unfold F_336. unfold F_275. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_275. unfold F_336. unfold fst in HFabs0. unfold F_336 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern u2.
simpl (acr _ _ _ _). cbv beta. try unfold acr. try rewrite H. try rewrite H0. try unfold acr in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 126 ] *)

assert (H1 := Hind F_340). clear Hind.
assert (HFabs0 : fst (F_340 u3 u4 0 u1)).
apply H1. trivial_in 10. unfold snd. unfold F_340. unfold F_275. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_275. unfold F_340. unfold fst in HFabs0. unfold F_340 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u2.
pattern u3.
pattern u4.
simpl (acr _ _ _ _). cbv beta. try unfold acr. try rewrite H. try rewrite H0. try unfold acr in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 127 ] *)

assert (H1 := Hind F_344). clear Hind.
assert (HFabs0 : fst (F_344 u3 u4 0 u1)).
apply H1. trivial_in 11. unfold snd. unfold F_344. unfold F_275. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_275. unfold F_344. unfold fst in HFabs0. unfold F_344 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern u2.
simpl (acr _ _ _ _). cbv beta. try unfold acr. try rewrite H. try rewrite H0. try unfold acr in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 340 ] *)

unfold fst. unfold F_340.
auto.



	(* TAUTOLOGY on [ 344 ] *)

unfold fst. unfold F_344.
auto.



	(* SUBSUMPTION on [ 336 ] *)

rename u1 into _u2. rename u2 into _u3. rename u3 into _u4. rename u4 into _u1. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u1 into u1. 
unfold fst. unfold F_336. specialize true_158 with (u1 := u3) (u2 := u4). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_257 := fun f => exists F, In F LF_257 /\ exists e1, exists e2, exists e3, exists e4, f = F e1 e2 e3 e4.

Theorem all_true_257: forall F, In F LF_257 -> forall u1: nat, forall u2: nat, forall u3: nat, forall u4: PLAN, fst (F u1  u2  u3 u4).
Proof.
let n := constr:(4) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_257);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_257;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_257: forall (u2: nat) (u3: nat) (u4: nat) (u1: PLAN), (acr u1 u2 u3 u4) = (acr1 u1 u2 u3 u4).
Proof.
do 4 intro.
apply (all_true_257 F_257);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
