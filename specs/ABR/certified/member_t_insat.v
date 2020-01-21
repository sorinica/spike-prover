
Require Import member_t_insat_spec.



Definition type_LF_157 :=  nat ->  nat -> (Prop * (List.list term)).

Definition F_157 : type_LF_157:= (fun    u1 u2 => ((nat_eq u1 u2) = true -> (nat_eq u1 u2) = false -> False, (Term id_nat_eq ((model_nat u1):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::nil)).
Definition F_177 : type_LF_157:= (fun    u3 _ => (false = true -> (nat_eq 0 (S u3)) = false -> False, (Term id_false nil)::(Term id_true nil)::(Term id_nat_eq ((Term id_0 nil):: (Term id_S ((model_nat u3)::nil))::nil))::(Term id_false nil)::nil)).
Definition F_183 : type_LF_157:= (fun    u3 _ => (false = true -> (nat_eq (S u3) 0) = false -> False, (Term id_false nil)::(Term id_true nil)::(Term id_nat_eq ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_false nil)::nil)).
Definition F_171 : type_LF_157:= (fun     _ _ => (true = true -> (nat_eq 0 0) = false -> False, (Term id_true nil)::(Term id_true nil)::(Term id_nat_eq ((Term id_0 nil):: (Term id_0 nil)::nil))::(Term id_false nil)::nil)).
Definition F_189 : type_LF_157:= (fun    u3 u4 => ((nat_eq u3 u4) = true -> (nat_eq (S u3) (S u4)) = false -> False, (Term id_nat_eq ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((Term id_S ((model_nat u3)::nil)):: (Term id_S ((model_nat u4)::nil))::nil))::(Term id_false nil)::nil)).
Definition F_190 : type_LF_157:= (fun     _ _ => ((nat_eq 0 0) = false -> False, (Term id_nat_eq ((Term id_0 nil):: (Term id_0 nil)::nil))::(Term id_false nil)::nil)).
Definition F_196 : type_LF_157:= (fun     _ _ => (true = false -> False, (Term id_true nil)::(Term id_false nil)::nil)).

Definition LF_157 := [F_157, F_177, F_183, F_171, F_189, F_190, F_196].


Function f_157 (u1: nat) (u2: nat) {struct u2} : bool :=
 match u1, u2 with
| 0, 0 => true
| 0, (S u3) => true
| (S u3), 0 => true
| (S u3), (S u4) => true
end.

Lemma main_157 : forall F, In F LF_157 -> forall u1, forall u2, (forall F', In F' LF_157 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 157 ] *)

rename u1 into _u1. rename u2 into _u2. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_157 u1 u2). apply f_157_ind.

(* case [ 171 ] *)

intros _u1 _u2.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_171). clear HFabs0.
assert (HFabs0 : fst (F_171 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_171. unfold F_157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_157. unfold F_171.
auto.


(* case [ 177 ] *)

intros _u1 _u2.  intro eq_1. intro u3.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_177). clear HFabs0.
assert (HFabs0 : fst (F_177 u3 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_177. unfold F_157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_157. unfold F_177.
auto.


(* case [ 183 ] *)

intros _u1 _u2. intro u3.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_183). clear HFabs0.
assert (HFabs0 : fst (F_183 u3 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_183. unfold F_157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_157. unfold F_183.
auto.


(* case [ 189 ] *)

intros _u1 _u2. intro u3.  intro eq_1. intro u4.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_189). clear HFabs0.
assert (HFabs0 : fst (F_189 u3 u4)).
apply Hind. trivial_in 4. unfold snd. unfold F_189. unfold F_157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_157. unfold F_189.
auto.





	(* NEGATIVE CLASH on [ 177 ] *)

unfold fst. unfold F_177. intros. try discriminate.



	(* NEGATIVE CLASH on [ 183 ] *)

unfold fst. unfold F_183. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 171 ] *)

rename u1 into d_u1. rename u2 into d_u2. 

assert (H := Hind F_190). 
assert (HFabs0 : fst (F_190 0 0)).
apply H. trivial_in 5. unfold snd. unfold F_190. unfold F_171. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_171. unfold F_190.

unfold fst in HFabs0. unfold F_190 in HFabs0.
auto.



	(* REWRITING on [ 189 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_157). clear Hind.
assert (HFabs1 : fst (F_157 u3 u4)).
apply Res. trivial_in 0. unfold snd. unfold F_157. unfold F_189. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_189. unfold fst in HFabs1. unfold F_157 in HFabs1.   
pattern u3, u4. simpl (nat_eq _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 190 ] *)

rename u1 into d_u1. rename u2 into d_u2. 

assert (Res := Hind F_196). clear Hind.
assert (HFabs1 : fst (F_196 0 0)).
apply Res. trivial_in 6. unfold snd. unfold F_196. unfold F_190. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_190. unfold fst in HFabs1. unfold F_196 in HFabs1.    simpl. auto.



	(* NEGATIVE CLASH on [ 196 ] *)

unfold fst. unfold F_196. intros. try discriminate.



Qed.



(* the set of all formula instances from the proof *)
Definition S_157 := fun f => exists F, In F LF_157 /\ exists e1, exists e2, f = F e1 e2.

Theorem all_true_157: forall F, In F LF_157 -> forall u1: nat, forall u2: nat, fst (F u1  u2).
Proof.
let n := constr:(2) in
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


Theorem true_157: forall (u1: nat) (u2: nat), (nat_eq u1 u2) = true -> (nat_eq u1 u2) = false -> False.
Proof.
do 2 intro.
apply (all_true_157 F_157);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_200 :=  PLAN ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_200 : type_LF_200:= (fun   u2 u1 _ _ => ((memberT u1 u2) = true -> (memberT u1 u2) = false -> False, (Term id_memberT ((model_nat u1):: (model_PLAN u2)::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u2)::nil))::(Term id_false nil)::nil)).
Definition F_213 : type_LF_200:= (fun    _ u1 _ _ => (false = true -> (memberT u1 Nil) = false -> False, (Term id_false nil)::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Nil nil)::nil))::(Term id_false nil)::nil)).
Definition F_219 : type_LF_200:= (fun   u6 u1 u4 u5 => (true = true -> (memberT u1 (Cons (C u4 u5) u6)) = false -> (nat_eq u1 u4) = true -> False, (Term id_true nil)::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_225 : type_LF_200:= (fun   u6 u1 u4 u5 => ((memberT u1 u6) = true -> (memberT u1 (Cons (C u4 u5) u6)) = false -> (nat_eq u1 u4) = false -> False, (Term id_memberT ((model_nat u1):: (model_PLAN u6)::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_false nil)::nil)).
Definition F_237 : type_LF_200:= (fun   u6 u1 u4 _ => ((memberT u1 u6) = true -> true = false -> (nat_eq u1 u4) = false -> (nat_eq u1 u4) = true -> False, (Term id_memberT ((model_nat u1):: (model_PLAN u6)::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_226 : type_LF_200:= (fun   u6 u1 u4 u5 => ((memberT u1 (Cons (C u4 u5) u6)) = false -> (nat_eq u1 u4) = true -> False, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_251 : type_LF_200:= (fun    _ u1 u4 _ => (true = false -> (nat_eq u1 u4) = true -> (nat_eq u1 u4) = true -> False, (Term id_true nil)::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_255 : type_LF_200:= (fun   u6 u1 u4 _ => ((memberT u1 u6) = false -> (nat_eq u1 u4) = true -> (nat_eq u1 u4) = false -> False, (Term id_memberT ((model_nat u1):: (model_PLAN u6)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_false nil)::nil)).

Definition LF_200 := [F_200, F_213, F_219, F_225, F_237, F_226, F_251, F_255].


Function f_200 (u2: PLAN) (u1: nat) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons (C u4 u5) u6), _ => true
end.

Lemma main_200 : forall F, In F LF_200 -> forall u1, forall u2, forall u3, forall u4, (forall F', In F' LF_200 -> forall e1, forall e2, forall e3, forall e4, less (snd (F' e1 e2 e3 e4)) (snd (F u1 u2 u3 u4)) -> fst (F' e1 e2 e3 e4)) -> fst (F u1 u2 u3 u4).
Proof.
intros F HF u1 u2 u3 u4; case_In HF; intro Hind.

	(* GENERATE on [ 200 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_200 u2 u1). apply f_200_ind.

(* case [ 213 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_213). clear HFabs0.
assert (HFabs0 : fst (F_213 Nil _u1 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_213. unfold F_200. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_200. unfold F_213.
auto.



intros _u2 _u1. intro u4. intro u5. intro u6.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
case_eq (nat_eq _u1 u4); [intro H | intro H].

(* case [ 219 ] *)

assert (Hind := HFabs0 F_219). clear HFabs0.
assert (HFabs0 : fst (F_219 u6 _u1 u4 u5)).
apply Hind. trivial_in 2. unfold snd. unfold F_219. unfold F_200. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_200. unfold F_219. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 225 ] *)

assert (Hind := HFabs0 F_225). clear HFabs0.
assert (HFabs0 : fst (F_225 u6 _u1 u4 u5)).
apply Hind. trivial_in 3. unfold snd. unfold F_225. unfold F_200. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_200. unfold F_225. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 213 ] *)

unfold fst. unfold F_213. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 219 ] *)

rename u1 into _u6. rename u2 into _u1. rename u3 into _u4. rename u4 into _u5. 
rename _u6 into u6. rename _u1 into u1. rename _u4 into u4. rename _u5 into u5. 
assert (H := Hind F_226). 
assert (HFabs0 : fst (F_226 u6 u1 u4 u5)).
apply H. trivial_in 5. unfold snd. unfold F_226. unfold F_219. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_219. unfold F_226.

unfold fst in HFabs0. unfold F_226 in HFabs0.
auto.



	(* TOTAL CASE REWRITING on [ 225 ] *)

rename u1 into _u6. rename u2 into _u1. rename u3 into _u4. rename u4 into _u5. 
rename _u6 into u6. rename _u1 into u1. rename _u4 into u4. rename _u5 into u5. 
assert (H: ((nat_eq u1 u4) = true) \/ ((nat_eq u1 u4) = false)). 

destruct ((nat_eq u1 u4)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_237). clear Hind.
assert (HFabs0 : fst (F_237 u6 u1 u4 0)).
apply H1. trivial_in 4. unfold snd. unfold F_237. unfold F_225. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_225. unfold F_237. unfold fst in HFabs0. unfold F_237 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u4.
pattern u5.
pattern u6.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_200). clear Hind.
assert (HFabs0 : fst (F_200 u6 u1 0 0)).
apply H1. trivial_in 0. unfold snd. unfold F_200. unfold F_225. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_225. unfold F_200. unfold fst in HFabs0. unfold F_200 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u4.
pattern u5.
pattern u6.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 237 ] *)

unfold fst. unfold F_237. intros. try discriminate.



	(* TOTAL CASE REWRITING on [ 226 ] *)

rename u1 into _u6. rename u2 into _u1. rename u3 into _u4. rename u4 into _u5. 
rename _u6 into u6. rename _u1 into u1. rename _u4 into u4. rename _u5 into u5. 
assert (H: ((nat_eq u1 u4) = true) \/ ((nat_eq u1 u4) = false)). 

destruct ((nat_eq u1 u4)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_251). clear Hind.
assert (HFabs0 : fst (F_251 Nil u1 u4 0)).
apply H1. trivial_in 6. unfold snd. unfold F_251. unfold F_226. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_226. unfold F_251. unfold fst in HFabs0. unfold F_251 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u4.
pattern u5.
pattern u6.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_255). clear Hind.
assert (HFabs0 : fst (F_255 u6 u1 u4 0)).
apply H1. trivial_in 7. unfold snd. unfold F_255. unfold F_226. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_226. unfold F_255. unfold fst in HFabs0. unfold F_255 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u4.
pattern u5.
pattern u6.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 251 ] *)

unfold fst. unfold F_251. intros. try discriminate.



	(* SUBSUMPTION on [ 255 ] *)

rename u1 into _u6. rename u2 into _u1. rename u3 into _u4. rename u4 into d_u4. 
rename _u6 into u6. rename _u1 into u1. rename _u4 into u4. 
unfold fst. unfold F_255. specialize true_157 with (u1 := u1) (u2 := u4). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_200 := fun f => exists F, In F LF_200 /\ exists e1, exists e2, exists e3, exists e4, f = F e1 e2 e3 e4.

Theorem all_true_200: forall F, In F LF_200 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, fst (F u1 u2  u3  u4).
Proof.
let n := constr:(4) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_200);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_200;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_200: forall (u2: PLAN) (u1: nat), (memberT u1 u2) = true -> (memberT u1 u2) = false -> False.
Proof.
do 2 intro.
apply (all_true_200 F_200);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_258 :=  PLAN ->  nat ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_258 : type_LF_258:= (fun   u2 u1 u3 u4 _ _ => ((memberT u1 (insAt u2 u3 u4)) = true -> (memberT u1 u2) = false -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_insAt ((model_PLAN u2):: (model_nat u3):: (model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u2)::nil))::(Term id_false nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_272 : type_LF_258:= (fun    _ u1 u3 u4 _ _ => ((memberT u1 (Cons (C u3 u4) Nil)) = true -> (memberT u1 Nil) = false -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Nil nil)::nil))::(Term id_false nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_287 : type_LF_258:= (fun    _ u1 u3 u4 _ _ => ((memberT u1 (Cons (C u3 u4) Nil)) = true -> false = false -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::(Term id_false nil)::(Term id_false nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_278 : type_LF_258:= (fun   u7 u1 u3 u4 u9 u10 => ((memberT u1 (Cons (C u3 u4) (Cons (C u9 u10) u7))) = true -> (memberT u1 (Cons (C u9 u10) u7)) = false -> (le (time (C u9 u10)) u3) = true -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u9):: (model_nat u10)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_284 : type_LF_258:= (fun   u7 u1 u3 u4 u9 u10 => ((memberT u1 (insAt u7 u3 u4)) = true -> (memberT u1 (Cons (C u9 u10) u7)) = false -> (le (time (C u9 u10)) u3) = false -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_insAt ((model_PLAN u7):: (model_nat u3):: (model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u9):: (model_nat u10)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_288 : type_LF_258:= (fun    _ u1 u3 u4 _ _ => ((memberT u1 (Cons (C u3 u4) Nil)) = true -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_313 : type_LF_258:= (fun    _ u1 u3 _ _ _ => (true = true -> (nat_eq u1 u3) = true -> u1 = u3, (Term id_true nil)::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_317 : type_LF_258:= (fun    _ u1 u3 _ _ _ => ((memberT u1 Nil) = true -> (nat_eq u1 u3) = false -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_Nil nil)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_false nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_321 : type_LF_258:= (fun    _ u1 u3 _ _ _ => (false = true -> (nat_eq u1 u3) = false -> u1 = u3, (Term id_false nil)::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_false nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_291 : type_LF_258:= (fun   u7 u1 u3 u4 u9 u10 => ((memberT u1 (Cons (C u3 u4) (Cons (C u9 u10) u7))) = true -> (memberT u1 (Cons (C u9 u10) u7)) = false -> (le u9 u3) = true -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_false nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_329 : type_LF_258:= (fun   u7 u1 u3 u4 u9 u10 => ((memberT u1 (Cons (C u3 u4) (Cons (C u9 u10) u7))) = true -> true = false -> (le u9 u3) = true -> (nat_eq u1 u9) = true -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_false nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_true nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_333 : type_LF_258:= (fun   u7 u1 u3 u4 u9 u10 => ((memberT u1 (Cons (C u3 u4) (Cons (C u9 u10) u7))) = true -> (memberT u1 u7) = false -> (le u9 u3) = true -> (nat_eq u1 u9) = false -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_345 : type_LF_258:= (fun   u7 u1 u3 u9 _ _ => (true = true -> (memberT u1 u7) = false -> (le u9 u3) = true -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = true -> u1 = u3, (Term id_true nil)::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_349 : type_LF_258:= (fun   u7 u1 u3 u9 u10 _ => ((memberT u1 (Cons (C u9 u10) u7)) = true -> (memberT u1 u7) = false -> (le u9 u3) = true -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = false -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_false nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_370 : type_LF_258:= (fun   u7 u1 u3 u9 _ _ => (true = true -> (memberT u1 u7) = false -> (le u9 u3) = true -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = false -> (nat_eq u1 u9) = true -> u1 = u3, (Term id_true nil)::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_true nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_374 : type_LF_258:= (fun   u7 u1 u3 u9 _ _ => ((memberT u1 u7) = true -> (memberT u1 u7) = false -> (le u9 u3) = true -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = false -> (nat_eq u1 u9) = false -> u1 = u3, (Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_375 : type_LF_258:= (fun   u7 u1 u3 u9 _ _ => ((memberT u1 u7) = false -> (le u9 u3) = true -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = false -> (nat_eq u1 u9) = true -> u1 = u3, (Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_true nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_294 : type_LF_258:= (fun   u7 u1 u3 u4 u9 u10 => ((memberT u1 (insAt u7 u3 u4)) = true -> (memberT u1 (Cons (C u9 u10) u7)) = false -> (le u9 u3) = false -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_insAt ((model_PLAN u7):: (model_nat u3):: (model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_false nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_false nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_386 : type_LF_258:= (fun   u7 u1 u3 u4 u9 _ => ((memberT u1 (insAt u7 u3 u4)) = true -> true = false -> (le u9 u3) = false -> (nat_eq u1 u9) = true -> u1 = u3, (Term id_memberT ((model_nat u1):: (Term id_insAt ((model_PLAN u7):: (model_nat u3):: (model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_false nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_true nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_318 : type_LF_258:= (fun    _ u1 u3 _ _ _ => ((nat_eq u1 u3) = true -> u1 = u3, (Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u1)::(model_nat u3)::nil)).
Definition F_409 : type_LF_258:= (fun    _  _ _ _ _ _ => (true = true -> 0 = 0, (Term id_true nil)::(Term id_true nil)::(Term id_0 nil)::(Term id_0 nil)::nil)).
Definition F_415 : type_LF_258:= (fun    _ u5 _ _ _ _ => (false = true -> 0 = (S u5), (Term id_false nil)::(Term id_true nil)::(Term id_0 nil)::(Term id_S ((model_nat u5)::nil))::nil)).
Definition F_421 : type_LF_258:= (fun    _ u5 _ _ _ _ => (false = true -> (S u5) = 0, (Term id_false nil)::(Term id_true nil)::(Term id_S ((model_nat u5)::nil))::(Term id_0 nil)::nil)).
Definition F_427 : type_LF_258:= (fun    _ u5 u6 _ _ _ => ((nat_eq u5 u6) = true -> (S u5) = (S u6), (Term id_nat_eq ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_S ((model_nat u5)::nil))::(Term id_S ((model_nat u6)::nil))::nil)).

Definition LF_258 := [F_258, F_272, F_287, F_278, F_284, F_288, F_313, F_317, F_321, F_291, F_329, F_333, F_345, F_349, F_370, F_374, F_375, F_294, F_386, F_318, F_409, F_415, F_421, F_427].


Function f_258 (u2: PLAN) (u3: nat) (u4: nat) {struct u2} : PLAN :=
 match u2, u3, u4 with
| Nil, _, _ => Nil
| (Cons (C u9 u10) u7), _, _ => Nil
end.

Function f_318 (u1: nat) (u3: nat) {struct u3} : bool :=
 match u1, u3 with
| 0, 0 => true
| 0, (S u5) => true
| (S u5), 0 => true
| (S u5), (S u6) => true
end.

Lemma main_258 : forall F, In F LF_258 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, (forall F', In F' LF_258 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, less (snd (F' e1 e2 e3 e4 e5 e6)) (snd (F u1 u2 u3 u4 u5 u6)) -> fst (F' e1 e2 e3 e4 e5 e6)) -> fst (F u1 u2 u3 u4 u5 u6).
Proof.
intros F HF u1 u2 u3 u4 u5 u6; case_In HF; intro Hind.

	(* GENERATE on [ 258 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. 

revert Hind.

pattern u2, u3, u4, (f_258 u2 u3 u4). apply f_258_ind.

(* case [ 272 ] *)

intros _u2 _u3 _u4.  intro eq_1. intro. intro Heq3. rewrite <- Heq3. intro. intro Heq4. rewrite <- Heq4.  intro HFabs0.
assert (Hind := HFabs0 F_272). clear HFabs0.
assert (HFabs0 : fst (F_272 Nil u1 _u3 _u4 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_272. unfold F_258. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_258. unfold F_272.
auto.



intros _u2 _u3 _u4. intro u9. intro u10. intro u7.  intro eq_1. intro. intro Heq3. rewrite <- Heq3. intro. intro Heq4. rewrite <- Heq4.  intro HFabs0.
case_eq (le (time (C u9 u10)) _u3); [intro H | intro H].

(* case [ 278 ] *)

assert (Hind := HFabs0 F_278). clear HFabs0.
assert (HFabs0 : fst (F_278 u7 u1 _u3 _u4 u9 u10)).
apply Hind. trivial_in 3. unfold snd. unfold F_278. unfold F_258. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_258. unfold F_278. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 284 ] *)

assert (Hind := HFabs0 F_284). clear HFabs0.
assert (HFabs0 : fst (F_284 u7 u1 _u3 _u4 u9 u10)).
apply Hind. trivial_in 4. unfold snd. unfold F_284. unfold F_258. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_258. unfold F_284. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* REWRITING on [ 272 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_287). clear Hind.
assert (HFabs1 : fst (F_287 Nil u1 u3 u4 0 0)).
apply Res. trivial_in 2. unfold snd. unfold F_287. unfold F_272. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_272. unfold fst in HFabs1. unfold F_287 in HFabs1.   
pattern u1. simpl (memberT _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE DECOMPOSITION on [ 287 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. 
assert (H := Hind F_288). 
assert (HFabs0 : fst (F_288 Nil u1 u3 u4 0 0)).
apply H. trivial_in 5. unfold snd. unfold F_288. unfold F_287. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_287. unfold F_288.

unfold fst in HFabs0. unfold F_288 in HFabs0.
auto.



	(* REWRITING on [ 278 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (Res := Hind F_291). clear Hind.
assert (HFabs1 : fst (F_291 u7 u1 u3 u4 u9 u10)).
apply Res. trivial_in 9. unfold snd. unfold F_291. unfold F_278. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_278. unfold fst in HFabs1. unfold F_291 in HFabs1.   
pattern u9, u10. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 284 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (Res := Hind F_294). clear Hind.
assert (HFabs1 : fst (F_294 u7 u1 u3 u4 u9 u10)).
apply Res. trivial_in 17. unfold snd. unfold F_294. unfold F_284. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_284. unfold fst in HFabs1. unfold F_294 in HFabs1.   
pattern u9, u10. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 288 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. 
assert (H: ((nat_eq u1 u3) = true) \/ ((nat_eq u1 u3) = false)). 

destruct ((nat_eq u1 u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_313). clear Hind.
assert (HFabs0 : fst (F_313 Nil u1 u3 0 0 0)).
apply H1. trivial_in 6. unfold snd. unfold F_313. unfold F_288. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_288. unfold F_313. unfold fst in HFabs0. unfold F_313 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern Nil.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_317). clear Hind.
assert (HFabs0 : fst (F_317 Nil u1 u3 0 0 0)).
apply H1. trivial_in 7. unfold snd. unfold F_317. unfold F_288. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_288. unfold F_317. unfold fst in HFabs0. unfold F_317 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern Nil.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE DECOMPOSITION on [ 313 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. rename _u3 into u3. 
assert (H := Hind F_318). 
assert (HFabs0 : fst (F_318 Nil u1 u3 0 0 0)).
apply H. trivial_in 19. unfold snd. unfold F_318. unfold F_313. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_313. unfold F_318.

unfold fst in HFabs0. unfold F_318 in HFabs0.
auto.



	(* REWRITING on [ 317 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. rename _u3 into u3. 
assert (Res := Hind F_321). clear Hind.
assert (HFabs1 : fst (F_321 Nil u1 u3 0 0 0)).
apply Res. trivial_in 8. unfold snd. unfold F_321. unfold F_317. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_317. unfold fst in HFabs1. unfold F_321 in HFabs1.   
pattern u1. simpl (memberT _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE CLASH on [ 321 ] *)

unfold fst. unfold F_321. intros. try discriminate.



	(* TOTAL CASE REWRITING on [ 291 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H: ((nat_eq u1 u9) = true) \/ ((nat_eq u1 u9) = false)). 

destruct ((nat_eq u1 u9)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_329). clear Hind.
assert (HFabs0 : fst (F_329 u7 u1 u3 u4 u9 u10)).
apply H1. trivial_in 10. unfold snd. unfold F_329. unfold F_291. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_291. unfold F_329. unfold fst in HFabs0. unfold F_329 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u10.
pattern u7.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_333). clear Hind.
assert (HFabs0 : fst (F_333 u7 u1 u3 u4 u9 u10)).
apply H1. trivial_in 11. unfold snd. unfold F_333. unfold F_291. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_291. unfold F_333. unfold fst in HFabs0. unfold F_333 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u10.
pattern u7.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 329 ] *)

unfold fst. unfold F_329. intros. try discriminate.



	(* TOTAL CASE REWRITING on [ 333 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H: ((nat_eq u1 u3) = true) \/ ((nat_eq u1 u3) = false)). 

destruct ((nat_eq u1 u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_345). clear Hind.
assert (HFabs0 : fst (F_345 u7 u1 u3 u9 0 0)).
apply H1. trivial_in 12. unfold snd. unfold F_345. unfold F_333. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_333. unfold F_345. unfold fst in HFabs0. unfold F_345 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern (Cons (C u9 u10) u7).
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_349). clear Hind.
assert (HFabs0 : fst (F_349 u7 u1 u3 u9 u10 0)).
apply H1. trivial_in 13. unfold snd. unfold F_349. unfold F_333. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_333. unfold F_349. unfold fst in HFabs0. unfold F_349 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern (Cons (C u9 u10) u7).
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE DECOMPOSITION on [ 345 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u9. rename u5 into d_u5. rename u6 into d_u6. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u9 into u9. 
assert (H := Hind F_318). 
assert (HFabs0 : fst (F_318 Nil u1 u3 0 0 0)).
apply H. trivial_in 19. unfold snd. unfold F_318. unfold F_345. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_345. unfold F_318.

unfold fst in HFabs0. unfold F_318 in HFabs0.
auto.



	(* TOTAL CASE REWRITING on [ 349 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u9. rename u5 into _u10. rename u6 into d_u6. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u9 into u9. rename _u10 into u10. 
assert (H: ((nat_eq u1 u9) = true) \/ ((nat_eq u1 u9) = false)). 

destruct ((nat_eq u1 u9)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_370). clear Hind.
assert (HFabs0 : fst (F_370 u7 u1 u3 u9 0 0)).
apply H1. trivial_in 14. unfold snd. unfold F_370. unfold F_349. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_349. unfold F_370. unfold fst in HFabs0. unfold F_370 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u10.
pattern u7.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_374). clear Hind.
assert (HFabs0 : fst (F_374 u7 u1 u3 u9 0 0)).
apply H1. trivial_in 15. unfold snd. unfold F_374. unfold F_349. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_349. unfold F_374. unfold fst in HFabs0. unfold F_374 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u10.
pattern u7.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE DECOMPOSITION on [ 370 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u9. rename u5 into d_u5. rename u6 into d_u6. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u9 into u9. 
assert (H := Hind F_375). 
assert (HFabs0 : fst (F_375 u7 u1 u3 u9 0 0)).
apply H. trivial_in 16. unfold snd. unfold F_375. unfold F_370. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_370. unfold F_375.

unfold fst in HFabs0. unfold F_375 in HFabs0.
auto.



	(* SUBSUMPTION on [ 374 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u9. rename u5 into d_u5. rename u6 into d_u6. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u9 into u9. 
unfold fst. unfold F_374. specialize true_200 with (u1 := u1) (u2 := u7). intro L. intros. contradict L. (auto || symmetry; auto).



	(* SUBSUMPTION on [ 375 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u9. rename u5 into d_u5. rename u6 into d_u6. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u9 into u9. 
unfold fst. unfold F_375. specialize true_157 with (u1 := u1) (u2 := u9). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 294 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H: ((nat_eq u1 u9) = true) \/ ((nat_eq u1 u9) = false)). 

destruct ((nat_eq u1 u9)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_386). clear Hind.
assert (HFabs0 : fst (F_386 u7 u1 u3 u4 u9 0)).
apply H1. trivial_in 18. unfold snd. unfold F_386. unfold F_294. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_294. unfold F_386. unfold fst in HFabs0. unfold F_386 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u10.
pattern u7.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_258). clear Hind.
assert (HFabs0 : fst (F_258 u7 u1 u3 u4 0 0)).
apply H1. trivial_in 0. unfold snd. unfold F_258. unfold F_294. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_294. unfold F_258. unfold fst in HFabs0. unfold F_258 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u10.
pattern u7.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 386 ] *)

unfold fst. unfold F_386. intros. try discriminate.



	(* GENERATE on [ 318 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. rename _u3 into u3. 

revert Hind.

pattern u1, u3, (f_318 u1 u3). apply f_318_ind.

(* case [ 409 ] *)

intros _u1 _u3.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_409). clear HFabs0.
assert (HFabs0 : fst (F_409 Nil 0 0 0 0 0)).
apply Hind. trivial_in 20. unfold snd. unfold F_409. unfold F_318. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_318. unfold F_409.
auto.


(* case [ 415 ] *)

intros _u1 _u3.  intro eq_1. intro u5.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_415). clear HFabs0.
assert (HFabs0 : fst (F_415 Nil u5 0 0 0 0)).
apply Hind. trivial_in 21. unfold snd. unfold F_415. unfold F_318. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_318. unfold F_415.
auto.


(* case [ 421 ] *)

intros _u1 _u3. intro u5.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_421). clear HFabs0.
assert (HFabs0 : fst (F_421 Nil u5 0 0 0 0)).
apply Hind. trivial_in 22. unfold snd. unfold F_421. unfold F_318. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_318. unfold F_421.
auto.


(* case [ 427 ] *)

intros _u1 _u3. intro u5.  intro eq_1. intro u6.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_427). clear HFabs0.
assert (HFabs0 : fst (F_427 Nil u5 u6 0 0 0)).
apply Hind. trivial_in 23. unfold snd. unfold F_427. unfold F_318. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_318. unfold F_427.
auto.





	(* TAUTOLOGY on [ 409 ] *)

unfold fst. unfold F_409.
auto.



	(* NEGATIVE CLASH on [ 415 ] *)

unfold fst. unfold F_415. intros. try discriminate.



	(* NEGATIVE CLASH on [ 421 ] *)

unfold fst. unfold F_421. intros. try discriminate.



	(* POSITIVE DECOMPOSITION on [ 427 ] *)

rename u1 into d_u1. rename u2 into _u5. rename u3 into _u6. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u5 into u5. rename _u6 into u6. 
assert (H1 := Hind F_318). 
assert (HFabs1 : fst (F_318 Nil u5 u6 0 0 0)).
apply H1. trivial_in 19. unfold snd. unfold F_318. unfold F_427. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_427. unfold F_318.

unfold fst in HFabs1. unfold F_318 in HFabs1.

repeat (auto || (rewrite HFabs1||  auto)).


Qed.



(* the set of all formula instances from the proof *)
Definition S_258 := fun f => exists F, In F LF_258 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, f = F e1 e2 e3 e4 e5 e6.

Theorem all_true_258: forall F, In F LF_258 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, fst (F u1 u2  u3  u4  u5  u6).
Proof.
let n := constr:(6) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_258);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_258;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_258: forall (u2: PLAN) (u1: nat) (u3: nat) (u4: nat), (memberT u1 (insAt u2 u3 u4)) = true -> (memberT u1 u2) = false -> u1 = u3.
Proof.
do 4 intro.
apply (all_true_258 F_258);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
