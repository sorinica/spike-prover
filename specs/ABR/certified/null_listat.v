
Require Import null_listat_spec.



Definition type_LF_156 :=  nat ->  nat -> (Prop * (List.list term)).

Definition F_156 : type_LF_156:= (fun    u1 u2 => ((le u1 u2) = false -> (le u1 u2) = true -> False, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_171 : type_LF_156:= (fun    u2 _ => (true = false -> (le 0 u2) = true -> False, (Term id_true nil)::(Term id_false nil)::(Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_177 : type_LF_156:= (fun    u3 _ => (false = false -> (le (S u3) 0) = true -> False, (Term id_false nil)::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_183 : type_LF_156:= (fun    u3 u4 => ((le u3 u4) = false -> (le (S u3) (S u4)) = true -> False, (Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_S ((model_nat u4)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_184 : type_LF_156:= (fun    u3 _ => ((le (S u3) 0) = true -> False, (Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_190 : type_LF_156:= (fun     _ _ => (false = true -> False, (Term id_false nil)::(Term id_true nil)::nil)).

Definition LF_156 := [F_156, F_171, F_177, F_183, F_184, F_190].


Function f_156 (u1: nat) (u2: nat) {struct u1} : bool :=
 match u1, u2 with
| 0, _ => true
| (S u3), 0 => true
| (S u3), (S u4) => true
end.

Lemma main_156 : forall F, In F LF_156 -> forall u1, forall u2, (forall F', In F' LF_156 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 156 ] *)

rename u1 into _u1. rename u2 into _u2. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_156 u1 u2). apply f_156_ind.

(* case [ 171 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_171). clear HFabs0.
assert (HFabs0 : fst (F_171 _u2 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_171. unfold F_156. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_156. unfold F_171.
auto.


(* case [ 177 ] *)

intros _u1 _u2. intro u3.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_177). clear HFabs0.
assert (HFabs0 : fst (F_177 u3 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_177. unfold F_156. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_156. unfold F_177.
auto.


(* case [ 183 ] *)

intros _u1 _u2. intro u3.  intro eq_1. intro u4.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_183). clear HFabs0.
assert (HFabs0 : fst (F_183 u3 u4)).
apply Hind. trivial_in 3. unfold snd. unfold F_183. unfold F_156. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_156. unfold F_183.
auto.





	(* NEGATIVE CLASH on [ 171 ] *)

unfold fst. unfold F_171. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 177 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (H := Hind F_184). 
assert (HFabs0 : fst (F_184 u3 0)).
apply H. trivial_in 4. unfold snd. unfold F_184. unfold F_177. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_177. unfold F_184.

unfold fst in HFabs0. unfold F_184 in HFabs0.
auto.



	(* REWRITING on [ 183 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_156). clear Hind.
assert (HFabs1 : fst (F_156 u3 u4)).
apply Res. trivial_in 0. unfold snd. unfold F_156. unfold F_183. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_183. unfold fst in HFabs1. unfold F_156 in HFabs1.   
pattern u3, u4. simpl (le _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 184 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (Res := Hind F_190). clear Hind.
assert (HFabs1 : fst (F_190 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_190. unfold F_184. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_184. unfold fst in HFabs1. unfold F_190 in HFabs1.   
pattern u3. simpl (le _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE CLASH on [ 190 ] *)

unfold fst. unfold F_190. intros. try discriminate.



Qed.



(* the set of all formula instances from the proof *)
Definition S_156 := fun f => exists F, In F LF_156 /\ exists e1, exists e2, f = F e1 e2.

Theorem all_true_156: forall F, In F LF_156 -> forall u1: nat, forall u2: nat, fst (F u1  u2).
Proof.
let n := constr:(2) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_156);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_156;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_156: forall (u1: nat) (u2: nat), (le u1 u2) = false -> (le u1 u2) = true -> False.
Proof.
do 2 intro.
apply (all_true_156 F_156);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_194 :=  PLAN ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_194 : type_LF_194:= (fun   u1 u2 _ _ => ((listAt u1 u2) = Nil -> (progAt u1 u2) = 0, (Term id_listAt ((model_PLAN u1):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_progAt ((model_PLAN u1):: (model_nat u2)::nil))::(Term id_0 nil)::nil)).
Definition F_213 : type_LF_194:= (fun   u5 u2 u6 u7 => ((Cons (C u6 u7) u5) = Nil -> (le (time (C u6 u7)) u2) = true -> (progAt (Cons (C u6 u7) u5) u2) = 0, (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::(Term id_Nil nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil)):: (model_nat u2)::nil))::(Term id_0 nil)::nil)).
Definition F_207 : type_LF_194:= (fun    _ u2 _ _ => (Nil = Nil -> (progAt Nil u2) = 0, (Term id_Nil nil)::(Term id_Nil nil)::(Term id_progAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_0 nil)::nil)).
Definition F_219 : type_LF_194:= (fun   u5 u2 u6 u7 => ((listAt u5 u2) = Nil -> (le (time (C u6 u7)) u2) = false -> (progAt (Cons (C u6 u7) u5) u2) = 0, (Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil)):: (model_nat u2)::nil))::(Term id_0 nil)::nil)).
Definition F_220 : type_LF_194:= (fun    _ u2 _ _ => ((progAt Nil u2) = 0, (Term id_progAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_0 nil)::nil)).
Definition F_226 : type_LF_194:= (fun    _  _ _ _ => (0 = 0, (Term id_0 nil)::(Term id_0 nil)::nil)).
Definition F_223 : type_LF_194:= (fun   u5 u2 u6 u7 => ((listAt u5 u2) = Nil -> (le u6 u2) = false -> (progAt (Cons (C u6 u7) u5) u2) = 0, (Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil)):: (model_nat u2)::nil))::(Term id_0 nil)::nil)).
Definition F_234 : type_LF_194:= (fun   u5 u2 u6 u7 => ((listAt u5 u2) = Nil -> (le u6 u2) = false -> (le (time (C u6 u7)) u2) = true -> (er (C u6 u7)) = 0, (Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(Term id_0 nil)::nil)).
Definition F_238 : type_LF_194:= (fun   u5 u2 u6 u7 => ((listAt u5 u2) = Nil -> (le u6 u2) = false -> (le (time (C u6 u7)) u2) = false -> (progAt u5 u2) = 0, (Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((model_PLAN u5):: (model_nat u2)::nil))::(Term id_0 nil)::nil)).
Definition F_241 : type_LF_194:= (fun   u5 u2 u6 u7 => ((listAt u5 u2) = Nil -> (le u6 u2) = false -> (le u6 u2) = true -> (er (C u6 u7)) = 0, (Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(Term id_0 nil)::nil)).
Definition F_247 : type_LF_194:= (fun   u5 u2 u6 u7 => ((listAt u5 u2) = Nil -> (le u6 u2) = false -> (le u6 u2) = true -> u7 = 0, (Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(model_nat u7)::(Term id_0 nil)::nil)).

Definition LF_194 := [F_194, F_213, F_207, F_219, F_220, F_226, F_223, F_234, F_238, F_241, F_247].


Function f_194 (u1: PLAN) (u2: nat) {struct u1} : PLAN :=
 match u1, u2 with
| Nil, _ => Nil
| (Cons (C u6 u7) u5), _ => Nil
end.

Lemma main_194 : forall F, In F LF_194 -> forall u1, forall u2, forall u3, forall u4, (forall F', In F' LF_194 -> forall e1, forall e2, forall e3, forall e4, less (snd (F' e1 e2 e3 e4)) (snd (F u1 u2 u3 u4)) -> fst (F' e1 e2 e3 e4)) -> fst (F u1 u2 u3 u4).
Proof.
intros F HF u1 u2 u3 u4; case_In HF; intro Hind.

	(* GENERATE on [ 194 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_194 u1 u2). apply f_194_ind.

(* case [ 207 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_207). clear HFabs0.
assert (HFabs0 : fst (F_207 Nil _u2 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_207. unfold F_194. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_194. unfold F_207.
auto.



intros _u1 _u2. intro u6. intro u7. intro u5.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
case_eq (le (time (C u6 u7)) _u2); [intro H | intro H].

(* case [ 213 ] *)

assert (Hind := HFabs0 F_213). clear HFabs0.
assert (HFabs0 : fst (F_213 u5 _u2 u6 u7)).
apply Hind. trivial_in 1. unfold snd. unfold F_213. unfold F_194. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_194. unfold F_213. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 219 ] *)

assert (Hind := HFabs0 F_219). clear HFabs0.
assert (HFabs0 : fst (F_219 u5 _u2 u6 u7)).
apply Hind. trivial_in 3. unfold snd. unfold F_219. unfold F_194. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_194. unfold F_219. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 213 ] *)

unfold fst. unfold F_213. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 207 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. 
rename _u2 into u2. 
assert (H := Hind F_220). 
assert (HFabs0 : fst (F_220 Nil u2 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_220. unfold F_207. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_207. unfold F_220.

unfold fst in HFabs0. unfold F_220 in HFabs0.
auto.



	(* REWRITING on [ 219 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_223). clear Hind.
assert (HFabs1 : fst (F_223 u5 u2 u6 u7)).
apply Res. trivial_in 6. unfold snd. unfold F_223. unfold F_219. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_219. unfold fst in HFabs1. unfold F_223 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 220 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. 
rename _u2 into u2. 
assert (Res := Hind F_226). clear Hind.
assert (HFabs1 : fst (F_226 Nil 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_226. unfold F_220. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_220. unfold fst in HFabs1. unfold F_226 in HFabs1.   
pattern u2. simpl (progAt _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 226 ] *)

unfold fst. unfold F_226.
auto.



	(* TOTAL CASE REWRITING on [ 223 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u6 u7)) u2) = true) \/ ((le (time (C u6 u7)) u2) = false)). 

destruct ((le (time (C u6 u7)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_234). clear Hind.
assert (HFabs0 : fst (F_234 u5 u2 u6 u7)).
apply H1. trivial_in 7. unfold snd. unfold F_234. unfold F_223. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_223. unfold F_234. unfold fst in HFabs0. unfold F_234 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern u5.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_238). clear Hind.
assert (HFabs0 : fst (F_238 u5 u2 u6 u7)).
apply H1. trivial_in 8. unfold snd. unfold F_238. unfold F_223. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_223. unfold F_238. unfold fst in HFabs0. unfold F_238 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern u5.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 234 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_241). clear Hind.
assert (HFabs1 : fst (F_241 u5 u2 u6 u7)).
apply Res. trivial_in 9. unfold snd. unfold F_241. unfold F_234. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_234. unfold fst in HFabs1. unfold F_241 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 238 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_194). clear Hind.
assert (HFabs1 : fst (F_194 u5 u2 0 0)).
apply Res. trivial_in 0. unfold snd. unfold F_194. unfold F_238. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_238. unfold fst in HFabs1. unfold F_194 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 241 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_247). clear Hind.
assert (HFabs1 : fst (F_247 u5 u2 u6 u7)).
apply Res. trivial_in 10. unfold snd. unfold F_247. unfold F_241. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_241. unfold fst in HFabs1. unfold F_247 in HFabs1.   
pattern u6, u7. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 247 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
unfold fst. unfold F_247. specialize true_156 with (u1 := u6) (u2 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_194 := fun f => exists F, In F LF_194 /\ exists e1, exists e2, exists e3, exists e4, f = F e1 e2 e3 e4.

Theorem all_true_194: forall F, In F LF_194 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, fst (F u1 u2  u3  u4).
Proof.
let n := constr:(4) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_194);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_194;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_194: forall (u1: PLAN) (u2: nat), (listAt u1 u2) = Nil -> (progAt u1 u2) = 0.
Proof.
do 2 intro.
apply (all_true_194 F_194);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
