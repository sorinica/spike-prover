
Require Import member_t_insin_spec.



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
Definition F_240 : type_LF_200:= (fun   u6 u1 u4 _ => ((memberT u1 u6) = true -> true = false -> (nat_eq u1 u4) = false -> (nat_eq u1 u4) = true -> False, (Term id_memberT ((model_nat u1):: (model_PLAN u6)::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_226 : type_LF_200:= (fun   u6 u1 u4 u5 => ((memberT u1 (Cons (C u4 u5) u6)) = false -> (nat_eq u1 u4) = true -> False, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_256 : type_LF_200:= (fun    _ u1 u4 _ => (true = false -> (nat_eq u1 u4) = true -> (nat_eq u1 u4) = true -> False, (Term id_true nil)::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_260 : type_LF_200:= (fun   u6 u1 u4 _ => ((memberT u1 u6) = false -> (nat_eq u1 u4) = true -> (nat_eq u1 u4) = false -> False, (Term id_memberT ((model_nat u1):: (model_PLAN u6)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u4)::nil))::(Term id_false nil)::nil)).

Definition LF_200 := [F_200, F_213, F_219, F_225, F_240, F_226, F_256, F_260].


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

assert (H1 := Hind F_240). clear Hind.
assert (HFabs0 : fst (F_240 u6 u1 u4 0)).
apply H1. trivial_in 4. unfold snd. unfold F_240. unfold F_225. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_225. unfold F_240. unfold fst in HFabs0. unfold F_240 in HFabs0. simpl in HFabs0. 
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



	(* NEGATIVE CLASH on [ 240 ] *)

unfold fst. unfold F_240. intros. try discriminate.



	(* TOTAL CASE REWRITING on [ 226 ] *)

rename u1 into _u6. rename u2 into _u1. rename u3 into _u4. rename u4 into _u5. 
rename _u6 into u6. rename _u1 into u1. rename _u4 into u4. rename _u5 into u5. 
assert (H: ((nat_eq u1 u4) = true) \/ ((nat_eq u1 u4) = false)). 

destruct ((nat_eq u1 u4)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_256). clear Hind.
assert (HFabs0 : fst (F_256 Nil u1 u4 0)).
apply H1. trivial_in 6. unfold snd. unfold F_256. unfold F_226. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_226. unfold F_256. unfold fst in HFabs0. unfold F_256 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u4.
pattern u5.
pattern u6.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_260). clear Hind.
assert (HFabs0 : fst (F_260 u6 u1 u4 0)).
apply H1. trivial_in 7. unfold snd. unfold F_260. unfold F_226. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_226. unfold F_260. unfold fst in HFabs0. unfold F_260 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u4.
pattern u5.
pattern u6.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 256 ] *)

unfold fst. unfold F_256. intros. try discriminate.



	(* SUBSUMPTION on [ 260 ] *)

rename u1 into _u6. rename u2 into _u1. rename u3 into _u4. rename u4 into d_u4. 
rename _u6 into u6. rename _u1 into u1. rename _u4 into u4. 
unfold fst. unfold F_260. specialize true_157 with (u1 := u1) (u2 := u4). intro L. intros. contradict L. (auto || symmetry; auto).



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


Definition type_LF_263 :=  PLAN ->  nat ->  nat ->  nat ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_263 : type_LF_263:= (fun   u2 u1 u3 u4 _ _ _ _ => ((memberT u1 (insIn u2 u3 u4)) = true -> (memberT u1 u2) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_insIn ((model_PLAN u2):: (model_nat u3):: (model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u2)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_277 : type_LF_263:= (fun    _ u1 u3 u4 _ _ _ _ => ((memberT u1 (Cons (C u3 u4) Nil)) = true -> (memberT u1 Nil) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Nil nil)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_292 : type_LF_263:= (fun    _ u1 u3 u4 _ _ _ _ => ((memberT u1 (Cons (C u3 u4) Nil)) = true -> false = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::(Term id_false nil)::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_283 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 (insIn u7 (time (C u9 u10)) u4)) = true -> (memberT u1 (Cons (C u9 u10) u7)) = false -> (le (er (C u9 u10)) u4) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_insIn ((model_PLAN u7):: (Term id_time ((Term id_C ((model_nat u9):: (model_nat u10)::nil))::nil)):: (model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_false nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u9):: (model_nat u10)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_289 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 (Cons (C u3 u4) (Cons (C u9 u10) u7))) = true -> (memberT u1 (Cons (C u9 u10) u7)) = false -> (le (er (C u9 u10)) u4) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_false nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u9):: (model_nat u10)::nil))::nil)):: (model_nat u4)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_296 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 (insIn u7 u9 u4)) = true -> (memberT u1 (Cons (C u9 u10) u7)) = false -> (le (er (C u9 u10)) u4) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_insIn ((model_PLAN u7):: (model_nat u9):: (model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_false nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u9):: (model_nat u10)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_299 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 (Cons (C u3 u4) (Cons (C u9 u10) u7))) = true -> (memberT u1 (Cons (C u9 u10) u7)) = false -> (le u10 u4) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_330 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 (Cons (C u3 u4) (Cons (C u9 u10) u7))) = true -> true = false -> (le u10 u4) = false -> (nat_eq u1 u9) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_334 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 (Cons (C u3 u4) (Cons (C u9 u10) u7))) = true -> (memberT u1 u7) = false -> (le u10 u4) = false -> (nat_eq u1 u9) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_354 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => (true = true -> (memberT u1 u7) = false -> (le u10 u4) = false -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = true -> u3 = u1, (Term id_true nil)::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_358 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 (Cons (C u9 u10) u7)) = true -> (memberT u1 u7) = false -> (le u10 u4) = false -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_391 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => (true = true -> (memberT u1 u7) = false -> (le u10 u4) = false -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = false -> (nat_eq u1 u9) = true -> u3 = u1, (Term id_true nil)::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_395 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 u7) = true -> (memberT u1 u7) = false -> (le u10 u4) = false -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = false -> (nat_eq u1 u9) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_396 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 u7) = false -> (le u10 u4) = false -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = false -> (nat_eq u1 u9) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_293 : type_LF_263:= (fun    _ u1 u3 u4 _ _ _ _ => ((memberT u1 (Cons (C u3 u4) Nil)) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_418 : type_LF_263:= (fun    _ u1 u3 _ _ _ _ _ => (true = true -> (nat_eq u1 u3) = true -> u3 = u1, (Term id_true nil)::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_422 : type_LF_263:= (fun    _ u1 u3 _ _ _ _ _ => ((memberT u1 Nil) = true -> (nat_eq u1 u3) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Nil nil)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_426 : type_LF_263:= (fun    _ u1 u3 _ _ _ _ _ => (false = true -> (nat_eq u1 u3) = false -> u3 = u1, (Term id_false nil)::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_302 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 (insIn u7 u9 u4)) = true -> (memberT u1 (Cons (C u9 u10) u7)) = false -> (le u10 u4) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_insIn ((model_PLAN u7):: (model_nat u9):: (model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u10)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_448 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 (insIn u7 u9 u4)) = true -> true = false -> (le u10 u4) = true -> (nat_eq u1 u9) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_insIn ((model_PLAN u7):: (model_nat u9):: (model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_452 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 (insIn u7 u9 u4)) = true -> (memberT u1 u7) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_insIn ((model_PLAN u7):: (model_nat u9):: (model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_487 : type_LF_263:= (fun    _ u1 u3 u4 u9 u10 _ _ => ((memberT u1 (Cons (C u9 u4) Nil)) = true -> (memberT u1 Nil) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Nil nil)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_502 : type_LF_263:= (fun    _ u1 u3 u4 u9 u10 _ _ => ((memberT u1 (Cons (C u9 u4) Nil)) = true -> false = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::(Term id_false nil)::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_493 : type_LF_263:= (fun   u13 u1 u3 u4 u9 u10 u15 u16 => ((memberT u1 (insIn u13 (time (C u15 u16)) u4)) = true -> (memberT u1 (Cons (C u15 u16) u13)) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (le (er (C u15 u16)) u4) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_insIn ((model_PLAN u13):: (Term id_time ((Term id_C ((model_nat u15):: (model_nat u16)::nil))::nil)):: (model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u15):: (model_nat u16)::nil)):: (model_PLAN u13)::nil))::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u15):: (model_nat u16)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_499 : type_LF_263:= (fun   u13 u1 u3 u4 u9 u10 u15 u16 => ((memberT u1 (Cons (C u9 u4) (Cons (C u15 u16) u13))) = true -> (memberT u1 (Cons (C u15 u16) u13)) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (le (er (C u15 u16)) u4) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u15):: (model_nat u16)::nil)):: (model_PLAN u13)::nil))::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u15):: (model_nat u16)::nil)):: (model_PLAN u13)::nil))::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u15):: (model_nat u16)::nil))::nil)):: (model_nat u4)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_506 : type_LF_263:= (fun   u13 u1 u3 u4 u9 u10 u15 u16 => ((memberT u1 (insIn u13 u15 u4)) = true -> (memberT u1 (Cons (C u15 u16) u13)) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (le (er (C u15 u16)) u4) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_insIn ((model_PLAN u13):: (model_nat u15):: (model_nat u4)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u15):: (model_nat u16)::nil)):: (model_PLAN u13)::nil))::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u15):: (model_nat u16)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_509 : type_LF_263:= (fun   u13 u1 u3 u4 u9 u10 u15 u16 => ((memberT u1 (Cons (C u9 u4) (Cons (C u15 u16) u13))) = true -> (memberT u1 (Cons (C u15 u16) u13)) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (le u16 u4) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u15):: (model_nat u16)::nil)):: (model_PLAN u13)::nil))::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u15):: (model_nat u16)::nil)):: (model_PLAN u13)::nil))::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_le ((model_nat u16):: (model_nat u4)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_577 : type_LF_263:= (fun   u13 u1 u3 u4 u9 u10 u15 u16 => ((memberT u1 (Cons (C u9 u4) (Cons (C u15 u16) u13))) = true -> true = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (le u16 u4) = false -> (nat_eq u1 u15) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u15):: (model_nat u16)::nil)):: (model_PLAN u13)::nil))::nil))::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_le ((model_nat u16):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u15)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_581 : type_LF_263:= (fun   u13 u1 u3 u4 u9 u10 u15 u16 => ((memberT u1 (Cons (C u9 u4) (Cons (C u15 u16) u13))) = true -> (memberT u1 u13) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (le u16 u4) = false -> (nat_eq u1 u15) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u15):: (model_nat u16)::nil)):: (model_PLAN u13)::nil))::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u13)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_le ((model_nat u16):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u15)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_625 : type_LF_263:= (fun   u13 u1 u3 u4 u9 u10 u15 u16 => (true = true -> (memberT u1 u13) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (le u16 u4) = false -> (nat_eq u1 u15) = false -> (nat_eq u1 u9) = true -> u3 = u1, (Term id_true nil)::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u13)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_le ((model_nat u16):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u15)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_630 : type_LF_263:= (fun   u13 u1 u3 u4 u9 u10 u15 u16 => ((memberT u1 u13) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (le u16 u4) = false -> (nat_eq u1 u15) = false -> (nat_eq u1 u9) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (model_PLAN u13)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_le ((model_nat u16):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u15)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_629 : type_LF_263:= (fun   u13 u1 u3 u4 u9 u10 u15 u16 => ((memberT u1 (Cons (C u15 u16) u13)) = true -> (memberT u1 u13) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (le u16 u4) = false -> (nat_eq u1 u15) = false -> (nat_eq u1 u9) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u15):: (model_nat u16)::nil)):: (model_PLAN u13)::nil))::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u13)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_le ((model_nat u16):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u15)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_678 : type_LF_263:= (fun   u13 u1 u3 u4 u9 u10 u15 u16 => (true = true -> (memberT u1 u13) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (le u16 u4) = false -> (nat_eq u1 u15) = false -> (nat_eq u1 u9) = false -> (nat_eq u1 u15) = true -> u3 = u1, (Term id_true nil)::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u13)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_le ((model_nat u16):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u15)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u15)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_682 : type_LF_263:= (fun   u13 u1 u3 u4 u9 u10 u15 u16 => ((memberT u1 u13) = true -> (memberT u1 u13) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (le u16 u4) = false -> (nat_eq u1 u15) = false -> (nat_eq u1 u9) = false -> (nat_eq u1 u15) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (model_PLAN u13)::nil))::(Term id_true nil)::(Term id_memberT ((model_nat u1):: (model_PLAN u13)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_le ((model_nat u16):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u15)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u15)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_683 : type_LF_263:= (fun   u13 u1 u3 u4 u9 u10 u15 u16 => ((memberT u1 u13) = false -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (le u16 u4) = false -> (nat_eq u1 u15) = false -> (nat_eq u1 u9) = false -> (nat_eq u1 u15) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (model_PLAN u13)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_le ((model_nat u16):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u15)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u15)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_503 : type_LF_263:= (fun    _ u1 u3 u4 u9 u10 _ _ => ((memberT u1 (Cons (C u9 u4) Nil)) = true -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Cons ((Term id_C ((model_nat u9):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_711 : type_LF_263:= (fun    _ u1 u3 u4 u9 u10 _ _ => (true = true -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (nat_eq u1 u9) = true -> u3 = u1, (Term id_true nil)::(Term id_true nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_715 : type_LF_263:= (fun    _ u1 u3 u4 u9 u10 _ _ => ((memberT u1 Nil) = true -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (nat_eq u1 u9) = false -> u3 = u1, (Term id_memberT ((model_nat u1):: (Term id_Nil nil)::nil))::(Term id_true nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_719 : type_LF_263:= (fun    _ u1 u3 u4 u9 u10 _ _ => (false = true -> (le u10 u4) = true -> (nat_eq u1 u9) = false -> (nat_eq u1 u9) = false -> u3 = u1, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_716 : type_LF_263:= (fun    _ u1 u3 u4 u9 u10 _ _ => ((le u10 u4) = true -> (nat_eq u1 u9) = false -> (nat_eq u1 u9) = true -> u3 = u1, (Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_359 : type_LF_263:= (fun   u7 u1 u3 u4 u9 u10 _ _ => ((memberT u1 u7) = false -> (le u10 u4) = false -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = true -> u3 = u1, (Term id_memberT ((model_nat u1):: (model_PLAN u7)::nil))::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_749 : type_LF_263:= (fun    _ u1 u3 u4 u9 u10 u12 _ => (true = false -> (le u10 u4) = false -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = true -> (nat_eq u1 u12) = true -> u3 = u1, (Term id_true nil)::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u12)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_743 : type_LF_263:= (fun    _ u1 u3 u4 u9 u10 _ _ => (false = false -> (le u10 u4) = false -> (nat_eq u1 u9) = false -> (nat_eq u1 u3) = true -> u3 = u1, (Term id_false nil)::(Term id_false nil)::(Term id_le ((model_nat u10):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u9)::nil))::(Term id_false nil)::(Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_423 : type_LF_263:= (fun    _ u1 u3 _ _ _ _ _ => ((nat_eq u1 u3) = true -> u3 = u1, (Term id_nat_eq ((model_nat u1):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u3)::(model_nat u1)::nil)).
Definition F_804 : type_LF_263:= (fun    _  _ _ _ _ _ _ _ => (true = true -> 0 = 0, (Term id_true nil)::(Term id_true nil)::(Term id_0 nil)::(Term id_0 nil)::nil)).
Definition F_810 : type_LF_263:= (fun    _ u5 _ _ _ _ _ _ => (false = true -> (S u5) = 0, (Term id_false nil)::(Term id_true nil)::(Term id_S ((model_nat u5)::nil))::(Term id_0 nil)::nil)).
Definition F_816 : type_LF_263:= (fun    _ u5 _ _ _ _ _ _ => (false = true -> 0 = (S u5), (Term id_false nil)::(Term id_true nil)::(Term id_0 nil)::(Term id_S ((model_nat u5)::nil))::nil)).
Definition F_822 : type_LF_263:= (fun    _ u5 u6 _ _ _ _ _ => ((nat_eq u5 u6) = true -> (S u6) = (S u5), (Term id_nat_eq ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_S ((model_nat u6)::nil))::(Term id_S ((model_nat u5)::nil))::nil)).

Definition LF_263 := [F_263, F_277, F_292, F_283, F_289, F_296, F_299, F_330, F_334, F_354, F_358, F_391, F_395, F_396, F_293, F_418, F_422, F_426, F_302, F_448, F_452, F_487, F_502, F_493, F_499, F_506, F_509, F_577, F_581, F_625, F_630, F_629, F_678, F_682, F_683, F_503, F_711, F_715, F_719, F_716, F_359, F_749, F_743, F_423, F_804, F_810, F_816, F_822].


Function f_263 (u2: PLAN) (u3: nat) (u4: nat) {struct u2} : PLAN :=
 match u2, u3, u4 with
| Nil, _, _ => Nil
| (Cons (C u9 u10) u7), _, _ => Nil
end.

Function f_452 (u7: PLAN) (u4: nat) (u9: nat) {struct u7} : PLAN :=
 match u7, u4, u9 with
| Nil, _, _ => Nil
| (Cons (C u15 u16) u13), _, _ => Nil
end.

Function f_359 (u7: PLAN) (u1: nat) {struct u7} : bool :=
 match u7, u1 with
| Nil, _ => true
| (Cons (C u12 u13) u14), _ => true
end.

Function f_423 (u1: nat) (u3: nat) {struct u3} : bool :=
 match u1, u3 with
| 0, 0 => true
| 0, (S u5) => true
| (S u5), 0 => true
| (S u5), (S u6) => true
end.

Lemma main_263 : forall F, In F LF_263 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, forall u7, forall u8, (forall F', In F' LF_263 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, forall e7, forall e8, less (snd (F' e1 e2 e3 e4 e5 e6 e7 e8)) (snd (F u1 u2 u3 u4 u5 u6 u7 u8)) -> fst (F' e1 e2 e3 e4 e5 e6 e7 e8)) -> fst (F u1 u2 u3 u4 u5 u6 u7 u8).
Proof.
intros F HF u1 u2 u3 u4 u5 u6 u7 u8; case_In HF; intro Hind.

	(* GENERATE on [ 263 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. 

revert Hind.

pattern u2, u3, u4, (f_263 u2 u3 u4). apply f_263_ind.

(* case [ 277 ] *)

intros _u2 _u3 _u4.  intro eq_1. intro. intro Heq3. rewrite <- Heq3. intro. intro Heq4. rewrite <- Heq4.  intro HFabs0.
assert (Hind := HFabs0 F_277). clear HFabs0.
assert (HFabs0 : fst (F_277 Nil u1 _u3 _u4 0 0 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_277. unfold F_263. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_263. unfold F_277.
auto.



intros _u2 _u3 _u4. intro u9. intro u10. intro u7.  intro eq_1. intro. intro Heq3. rewrite <- Heq3. intro. intro Heq4. rewrite <- Heq4.  intro HFabs0.
case_eq (le (er (C u9 u10)) _u4); [intro H | intro H].

(* case [ 283 ] *)

assert (Hind := HFabs0 F_283). clear HFabs0.
assert (HFabs0 : fst (F_283 u7 u1 _u3 _u4 u9 u10 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_283. unfold F_263. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_263. unfold F_283. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 289 ] *)

assert (Hind := HFabs0 F_289). clear HFabs0.
assert (HFabs0 : fst (F_289 u7 u1 _u3 _u4 u9 u10 0 0)).
apply Hind. trivial_in 4. unfold snd. unfold F_289. unfold F_263. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_263. unfold F_289. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* REWRITING on [ 277 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_292). clear Hind.
assert (HFabs1 : fst (F_292 Nil u1 u3 u4 0 0 0 0)).
apply Res. trivial_in 2. unfold snd. unfold F_292. unfold F_277. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_277. unfold fst in HFabs1. unfold F_292 in HFabs1.   
pattern u1. simpl (memberT _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE DECOMPOSITION on [ 292 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. 
assert (H := Hind F_293). 
assert (HFabs0 : fst (F_293 Nil u1 u3 u4 0 0 0 0)).
apply H. trivial_in 14. unfold snd. unfold F_293. unfold F_292. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_292. unfold F_293.

unfold fst in HFabs0. unfold F_293 in HFabs0.
auto.



	(* REWRITING on [ 283 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (Res := Hind F_296). clear Hind.
assert (HFabs1 : fst (F_296 u7 u1 u3 u4 u9 u10 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_296. unfold F_283. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_283. unfold fst in HFabs1. unfold F_296 in HFabs1.   
pattern u9, u10. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 289 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (Res := Hind F_299). clear Hind.
assert (HFabs1 : fst (F_299 u7 u1 u3 u4 u9 u10 0 0)).
apply Res. trivial_in 6. unfold snd. unfold F_299. unfold F_289. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_289. unfold fst in HFabs1. unfold F_299 in HFabs1.   
pattern u9, u10. simpl (er _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 296 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (Res := Hind F_302). clear Hind.
assert (HFabs1 : fst (F_302 u7 u1 u3 u4 u9 u10 0 0)).
apply Res. trivial_in 18. unfold snd. unfold F_302. unfold F_296. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_296. unfold fst in HFabs1. unfold F_302 in HFabs1.   
pattern u9, u10. simpl (er _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 299 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H: ((nat_eq u1 u9) = true) \/ ((nat_eq u1 u9) = false)). 

destruct ((nat_eq u1 u9)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_330). clear Hind.
assert (HFabs0 : fst (F_330 u7 u1 u3 u4 u9 u10 0 0)).
apply H1. trivial_in 7. unfold snd. unfold F_330. unfold F_299. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_299. unfold F_330. unfold fst in HFabs0. unfold F_330 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u10.
pattern u7.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_334). clear Hind.
assert (HFabs0 : fst (F_334 u7 u1 u3 u4 u9 u10 0 0)).
apply H1. trivial_in 8. unfold snd. unfold F_334. unfold F_299. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_299. unfold F_334. unfold fst in HFabs0. unfold F_334 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u10.
pattern u7.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 330 ] *)

unfold fst. unfold F_330. intros. try discriminate.



	(* TOTAL CASE REWRITING on [ 334 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H: ((nat_eq u1 u3) = true) \/ ((nat_eq u1 u3) = false)). 

destruct ((nat_eq u1 u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_354). clear Hind.
assert (HFabs0 : fst (F_354 u7 u1 u3 u4 u9 u10 0 0)).
apply H1. trivial_in 9. unfold snd. unfold F_354. unfold F_334. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_334. unfold F_354. unfold fst in HFabs0. unfold F_354 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern (Cons (C u9 u10) u7).
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_358). clear Hind.
assert (HFabs0 : fst (F_358 u7 u1 u3 u4 u9 u10 0 0)).
apply H1. trivial_in 10. unfold snd. unfold F_358. unfold F_334. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_334. unfold F_358. unfold fst in HFabs0. unfold F_358 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern (Cons (C u9 u10) u7).
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE DECOMPOSITION on [ 354 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H := Hind F_359). 
assert (HFabs0 : fst (F_359 u7 u1 u3 u4 u9 u10 0 0)).
apply H. trivial_in 40. unfold snd. unfold F_359. unfold F_354. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_354. unfold F_359.

unfold fst in HFabs0. unfold F_359 in HFabs0.
auto.



	(* TOTAL CASE REWRITING on [ 358 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H: ((nat_eq u1 u9) = true) \/ ((nat_eq u1 u9) = false)). 

destruct ((nat_eq u1 u9)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_391). clear Hind.
assert (HFabs0 : fst (F_391 u7 u1 u3 u4 u9 u10 0 0)).
apply H1. trivial_in 11. unfold snd. unfold F_391. unfold F_358. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_358. unfold F_391. unfold fst in HFabs0. unfold F_391 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u10.
pattern u7.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_395). clear Hind.
assert (HFabs0 : fst (F_395 u7 u1 u3 u4 u9 u10 0 0)).
apply H1. trivial_in 12. unfold snd. unfold F_395. unfold F_358. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_358. unfold F_395. unfold fst in HFabs0. unfold F_395 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u10.
pattern u7.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE DECOMPOSITION on [ 391 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H := Hind F_396). 
assert (HFabs0 : fst (F_396 u7 u1 u3 u4 u9 u10 0 0)).
apply H. trivial_in 13. unfold snd. unfold F_396. unfold F_391. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_391. unfold F_396.

unfold fst in HFabs0. unfold F_396 in HFabs0.
auto.



	(* SUBSUMPTION on [ 395 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
unfold fst. unfold F_395. specialize true_200 with (u1 := u1) (u2 := u7). intro L. intros. contradict L. (auto || symmetry; auto).



	(* SUBSUMPTION on [ 396 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
unfold fst. unfold F_396. specialize true_157 with (u1 := u1) (u2 := u9). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 293 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. 
assert (H: ((nat_eq u1 u3) = true) \/ ((nat_eq u1 u3) = false)). 

destruct ((nat_eq u1 u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_418). clear Hind.
assert (HFabs0 : fst (F_418 Nil u1 u3 0 0 0 0 0)).
apply H1. trivial_in 15. unfold snd. unfold F_418. unfold F_293. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_293. unfold F_418. unfold fst in HFabs0. unfold F_418 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern Nil.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_422). clear Hind.
assert (HFabs0 : fst (F_422 Nil u1 u3 0 0 0 0 0)).
apply H1. trivial_in 16. unfold snd. unfold F_422. unfold F_293. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_293. unfold F_422. unfold fst in HFabs0. unfold F_422 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u3.
pattern u4.
pattern Nil.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE DECOMPOSITION on [ 418 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. 
assert (H := Hind F_423). 
assert (HFabs0 : fst (F_423 Nil u1 u3 0 0 0 0 0)).
apply H. trivial_in 43. unfold snd. unfold F_423. unfold F_418. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_418. unfold F_423.

unfold fst in HFabs0. unfold F_423 in HFabs0.
auto.



	(* REWRITING on [ 422 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. 
assert (Res := Hind F_426). clear Hind.
assert (HFabs1 : fst (F_426 Nil u1 u3 0 0 0 0 0)).
apply Res. trivial_in 17. unfold snd. unfold F_426. unfold F_422. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_422. unfold fst in HFabs1. unfold F_426 in HFabs1.   
pattern u1. simpl (memberT _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE CLASH on [ 426 ] *)

unfold fst. unfold F_426. intros. try discriminate.



	(* TOTAL CASE REWRITING on [ 302 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H: ((nat_eq u1 u9) = true) \/ ((nat_eq u1 u9) = false)). 

destruct ((nat_eq u1 u9)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_448). clear Hind.
assert (HFabs0 : fst (F_448 u7 u1 u3 u4 u9 u10 0 0)).
apply H1. trivial_in 19. unfold snd. unfold F_448. unfold F_302. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_302. unfold F_448. unfold fst in HFabs0. unfold F_448 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u10.
pattern u7.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_452). clear Hind.
assert (HFabs0 : fst (F_452 u7 u1 u3 u4 u9 u10 0 0)).
apply H1. trivial_in 20. unfold snd. unfold F_452. unfold F_302. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_302. unfold F_452. unfold fst in HFabs0. unfold F_452 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u10.
pattern u7.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 448 ] *)

unfold fst. unfold F_448. intros. try discriminate.



	(* GENERATE on [ 452 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 

revert Hind.

pattern u7, u4, u9, (f_452 u7 u4 u9). apply f_452_ind.

(* case [ 487 ] *)

intros _u7 _u4 _u9.  intro eq_1. intro. intro Heq4. rewrite <- Heq4. intro. intro Heq9. rewrite <- Heq9.  intro HFabs0.
assert (Hind := HFabs0 F_487). clear HFabs0.
assert (HFabs0 : fst (F_487 Nil u1 u3 _u4 _u9 u10 0 0)).
apply Hind. trivial_in 21. unfold snd. unfold F_487. unfold F_452. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_452. unfold F_487.
auto.



intros _u7 _u4 _u9. intro u15. intro u16. intro u13.  intro eq_1. intro. intro Heq4. rewrite <- Heq4. intro. intro Heq9. rewrite <- Heq9.  intro HFabs0.
case_eq (le (er (C u15 u16)) _u4); [intro H | intro H].

(* case [ 493 ] *)

assert (Hind := HFabs0 F_493). clear HFabs0.
assert (HFabs0 : fst (F_493 u13 u1 u3 _u4 _u9 u10 u15 u16)).
apply Hind. trivial_in 23. unfold snd. unfold F_493. unfold F_452. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_452. unfold F_493. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 499 ] *)

assert (Hind := HFabs0 F_499). clear HFabs0.
assert (HFabs0 : fst (F_499 u13 u1 u3 _u4 _u9 u10 u15 u16)).
apply Hind. trivial_in 24. unfold snd. unfold F_499. unfold F_452. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_452. unfold F_499. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* REWRITING on [ 487 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (Res := Hind F_502). clear Hind.
assert (HFabs1 : fst (F_502 Nil u1 u3 u4 u9 u10 0 0)).
apply Res. trivial_in 22. unfold snd. unfold F_502. unfold F_487. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_487. unfold fst in HFabs1. unfold F_502 in HFabs1.   
pattern u1. simpl (memberT _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE DECOMPOSITION on [ 502 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H := Hind F_503). 
assert (HFabs0 : fst (F_503 Nil u1 u3 u4 u9 u10 0 0)).
apply H. trivial_in 35. unfold snd. unfold F_503. unfold F_502. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_502. unfold F_503.

unfold fst in HFabs0. unfold F_503 in HFabs0.
auto.



	(* REWRITING on [ 493 ] *)

rename u1 into _u13. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into _u15. rename u8 into _u16. 
rename _u13 into u13. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. rename _u15 into u15. rename _u16 into u16. 
assert (Res := Hind F_506). clear Hind.
assert (HFabs1 : fst (F_506 u13 u1 u3 u4 u9 u10 u15 u16)).
apply Res. trivial_in 25. unfold snd. unfold F_506. unfold F_493. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_493. unfold fst in HFabs1. unfold F_506 in HFabs1.   
pattern u15, u16. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 499 ] *)

rename u1 into _u13. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into _u15. rename u8 into _u16. 
rename _u13 into u13. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. rename _u15 into u15. rename _u16 into u16. 
assert (Res := Hind F_509). clear Hind.
assert (HFabs1 : fst (F_509 u13 u1 u3 u4 u9 u10 u15 u16)).
apply Res. trivial_in 26. unfold snd. unfold F_509. unfold F_499. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_499. unfold fst in HFabs1. unfold F_509 in HFabs1.   
pattern u15, u16. simpl (er _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 506 ] *)

rename u1 into _u13. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into _u15. rename u8 into _u16. 
rename _u13 into u13. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. rename _u15 into u15. rename _u16 into u16. 
assert (Res := Hind F_302). clear Hind.
assert (HFabs1 : fst (F_302 u13 u1 u3 u4 u15 u16 0 0)).
apply Res. trivial_in 18. unfold snd. unfold F_302. unfold F_506. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_506. unfold fst in HFabs1. unfold F_302 in HFabs1.   
pattern u15, u16. simpl (er _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 509 ] *)

rename u1 into _u13. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into _u15. rename u8 into _u16. 
rename _u13 into u13. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. rename _u15 into u15. rename _u16 into u16. 
assert (H: ((nat_eq u1 u15) = true) \/ ((nat_eq u1 u15) = false)). 

destruct ((nat_eq u1 u15)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_577). clear Hind.
assert (HFabs0 : fst (F_577 u13 u1 u3 u4 u9 u10 u15 u16)).
apply H1. trivial_in 27. unfold snd. unfold F_577. unfold F_509. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_509. unfold F_577. unfold fst in HFabs0. unfold F_577 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u15.
pattern u16.
pattern u13.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_581). clear Hind.
assert (HFabs0 : fst (F_581 u13 u1 u3 u4 u9 u10 u15 u16)).
apply H1. trivial_in 28. unfold snd. unfold F_581. unfold F_509. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_509. unfold F_581. unfold fst in HFabs0. unfold F_581 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u15.
pattern u16.
pattern u13.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 577 ] *)

unfold fst. unfold F_577. intros. try discriminate.



	(* TOTAL CASE REWRITING on [ 581 ] *)

rename u1 into _u13. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into _u15. rename u8 into _u16. 
rename _u13 into u13. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. rename _u15 into u15. rename _u16 into u16. 
assert (H: ((nat_eq u1 u9) = true) \/ ((nat_eq u1 u9) = false)). 

destruct ((nat_eq u1 u9)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_625). clear Hind.
assert (HFabs0 : fst (F_625 u13 u1 u3 u4 u9 u10 u15 u16)).
apply H1. trivial_in 29. unfold snd. unfold F_625. unfold F_581. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_581. unfold F_625. unfold fst in HFabs0. unfold F_625 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u4.
pattern (Cons (C u15 u16) u13).
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_629). clear Hind.
assert (HFabs0 : fst (F_629 u13 u1 u3 u4 u9 u10 u15 u16)).
apply H1. trivial_in 31. unfold snd. unfold F_629. unfold F_581. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_581. unfold F_629. unfold fst in HFabs0. unfold F_629 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u4.
pattern (Cons (C u15 u16) u13).
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE DECOMPOSITION on [ 625 ] *)

rename u1 into _u13. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into _u15. rename u8 into _u16. 
rename _u13 into u13. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. rename _u15 into u15. rename _u16 into u16. 
assert (H := Hind F_630). 
assert (HFabs0 : fst (F_630 u13 u1 u3 u4 u9 u10 u15 u16)).
apply H. trivial_in 30. unfold snd. unfold F_630. unfold F_625. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_625. unfold F_630.

unfold fst in HFabs0. unfold F_630 in HFabs0.
auto.



	(* SUBSUMPTION on [ 630 ] *)

rename u1 into _u13. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into _u15. rename u8 into _u16. 
rename _u13 into u13. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. rename _u15 into u15. rename _u16 into u16. 
unfold fst. unfold F_630. specialize true_157 with (u1 := u1) (u2 := u9). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 629 ] *)

rename u1 into _u13. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into _u15. rename u8 into _u16. 
rename _u13 into u13. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. rename _u15 into u15. rename _u16 into u16. 
assert (H: ((nat_eq u1 u15) = true) \/ ((nat_eq u1 u15) = false)). 

destruct ((nat_eq u1 u15)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_678). clear Hind.
assert (HFabs0 : fst (F_678 u13 u1 u3 u4 u9 u10 u15 u16)).
apply H1. trivial_in 32. unfold snd. unfold F_678. unfold F_629. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_629. unfold F_678. unfold fst in HFabs0. unfold F_678 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u15.
pattern u16.
pattern u13.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_682). clear Hind.
assert (HFabs0 : fst (F_682 u13 u1 u3 u4 u9 u10 u15 u16)).
apply H1. trivial_in 33. unfold snd. unfold F_682. unfold F_629. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_629. unfold F_682. unfold fst in HFabs0. unfold F_682 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u15.
pattern u16.
pattern u13.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE DECOMPOSITION on [ 678 ] *)

rename u1 into _u13. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into _u15. rename u8 into _u16. 
rename _u13 into u13. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. rename _u15 into u15. rename _u16 into u16. 
assert (H := Hind F_683). 
assert (HFabs0 : fst (F_683 u13 u1 u3 u4 u9 u10 u15 u16)).
apply H. trivial_in 34. unfold snd. unfold F_683. unfold F_678. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_678. unfold F_683.

unfold fst in HFabs0. unfold F_683 in HFabs0.
auto.



	(* SUBSUMPTION on [ 682 ] *)

rename u1 into _u13. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into _u15. rename u8 into _u16. 
rename _u13 into u13. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. rename _u15 into u15. rename _u16 into u16. 
unfold fst. unfold F_682. specialize true_200 with (u1 := u1) (u2 := u13). intro L. intros. contradict L. (auto || symmetry; auto).



	(* SUBSUMPTION on [ 683 ] *)

rename u1 into _u13. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into _u15. rename u8 into _u16. 
rename _u13 into u13. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. rename _u15 into u15. rename _u16 into u16. 
unfold fst. unfold F_683. specialize true_157 with (u1 := u1) (u2 := u15). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 503 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H: ((nat_eq u1 u9) = true) \/ ((nat_eq u1 u9) = false)). 

destruct ((nat_eq u1 u9)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 93 ] *)

assert (H1 := Hind F_711). clear Hind.
assert (HFabs0 : fst (F_711 Nil u1 u3 u4 u9 u10 0 0)).
apply H1. trivial_in 36. unfold snd. unfold F_711. unfold F_503. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_503. unfold F_711. unfold fst in HFabs0. unfold F_711 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u4.
pattern Nil.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 94 ] *)

assert (H1 := Hind F_715). clear Hind.
assert (HFabs0 : fst (F_715 Nil u1 u3 u4 u9 u10 0 0)).
apply H1. trivial_in 37. unfold snd. unfold F_715. unfold F_503. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_503. unfold F_715. unfold fst in HFabs0. unfold F_715 in HFabs0. simpl in HFabs0. 
pattern u1.
pattern u9.
pattern u4.
pattern Nil.
simpl (memberT _ _). cbv beta. try unfold memberT. try rewrite H. try rewrite H0. try unfold memberT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE DECOMPOSITION on [ 711 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H := Hind F_716). 
assert (HFabs0 : fst (F_716 Nil u1 u3 u4 u9 u10 0 0)).
apply H. trivial_in 39. unfold snd. unfold F_716. unfold F_711. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_711. unfold F_716.

unfold fst in HFabs0. unfold F_716 in HFabs0.
auto.



	(* REWRITING on [ 715 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (Res := Hind F_719). clear Hind.
assert (HFabs1 : fst (F_719 Nil u1 u3 u4 u9 u10 0 0)).
apply Res. trivial_in 38. unfold snd. unfold F_719. unfold F_715. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_715. unfold fst in HFabs1. unfold F_719 in HFabs1.   
pattern u1. simpl (memberT _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE CLASH on [ 719 ] *)

unfold fst. unfold F_719. intros. try discriminate.



	(* SUBSUMPTION on [ 716 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
unfold fst. unfold F_716. specialize true_157 with (u1 := u1) (u2 := u9). intro L. intros. contradict L. (auto || symmetry; auto).



	(* GENERATE on [ 359 ] *)

rename u1 into _u7. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u7 into u7. rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 

revert Hind.

pattern u7, u1, (f_359 u7 u1). apply f_359_ind.

(* case [ 743 ] *)

intros _u7 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_743). clear HFabs0.
assert (HFabs0 : fst (F_743 Nil _u1 u3 u4 u9 u10 0 0)).
apply Hind. trivial_in 42. unfold snd. unfold F_743. unfold F_359. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_359. unfold F_743.
auto.



intros _u7 _u1. intro u12. intro u13. intro u14.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
case_eq (nat_eq _u1 u12); [intro H | intro H].

(* case [ 749 ] *)

assert (Hind := HFabs0 F_749). clear HFabs0.
assert (HFabs0 : fst (F_749 Nil _u1 u3 u4 u9 u10 u12 0)).
apply Hind. trivial_in 41. unfold snd. unfold F_749. unfold F_359. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_359. unfold F_749. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 755 ] *)

assert (Hind := HFabs0 F_359). clear HFabs0.
assert (HFabs0 : fst (F_359 u14 _u1 u3 u4 u9 u10 0 0)).
apply Hind. trivial_in 40. unfold snd. unfold F_359. unfold F_359. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_359. unfold F_359. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 749 ] *)

unfold fst. unfold F_749. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 743 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into _u4. rename u5 into _u9. rename u6 into _u10. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. rename _u4 into u4. rename _u9 into u9. rename _u10 into u10. 
assert (H := Hind F_423). 
assert (HFabs0 : fst (F_423 Nil u1 u3 0 0 0 0 0)).
apply H. trivial_in 43. unfold snd. unfold F_423. unfold F_743. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_743. unfold F_423.

unfold fst in HFabs0. unfold F_423 in HFabs0.
auto.



	(* GENERATE on [ 423 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u3 into u3. 

revert Hind.

pattern u1, u3, (f_423 u1 u3). apply f_423_ind.

(* case [ 804 ] *)

intros _u1 _u3.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_804). clear HFabs0.
assert (HFabs0 : fst (F_804 Nil 0 0 0 0 0 0 0)).
apply Hind. trivial_in 44. unfold snd. unfold F_804. unfold F_423. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_423. unfold F_804.
auto.


(* case [ 810 ] *)

intros _u1 _u3.  intro eq_1. intro u5.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_810). clear HFabs0.
assert (HFabs0 : fst (F_810 Nil u5 0 0 0 0 0 0)).
apply Hind. trivial_in 45. unfold snd. unfold F_810. unfold F_423. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_423. unfold F_810.
auto.


(* case [ 816 ] *)

intros _u1 _u3. intro u5.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_816). clear HFabs0.
assert (HFabs0 : fst (F_816 Nil u5 0 0 0 0 0 0)).
apply Hind. trivial_in 46. unfold snd. unfold F_816. unfold F_423. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_423. unfold F_816.
auto.


(* case [ 822 ] *)

intros _u1 _u3. intro u5.  intro eq_1. intro u6.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_822). clear HFabs0.
assert (HFabs0 : fst (F_822 Nil u5 u6 0 0 0 0 0)).
apply Hind. trivial_in 47. unfold snd. unfold F_822. unfold F_423. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_423. unfold F_822.
auto.





	(* TAUTOLOGY on [ 804 ] *)

unfold fst. unfold F_804.
auto.



	(* NEGATIVE CLASH on [ 810 ] *)

unfold fst. unfold F_810. intros. try discriminate.



	(* NEGATIVE CLASH on [ 816 ] *)

unfold fst. unfold F_816. intros. try discriminate.



	(* POSITIVE DECOMPOSITION on [ 822 ] *)

rename u1 into d_u1. rename u2 into _u5. rename u3 into _u6. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u5 into u5. rename _u6 into u6. 
assert (H1 := Hind F_423). 
assert (HFabs1 : fst (F_423 Nil u5 u6 0 0 0 0 0)).
apply H1. trivial_in 43. unfold snd. unfold F_423. unfold F_822. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_822. unfold F_423.

unfold fst in HFabs1. unfold F_423 in HFabs1.

repeat (auto || (rewrite HFabs1||  auto)).


Qed.



(* the set of all formula instances from the proof *)
Definition S_263 := fun f => exists F, In F LF_263 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, exists e7, exists e8, f = F e1 e2 e3 e4 e5 e6 e7 e8.

Theorem all_true_263: forall F, In F LF_263 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, forall u7: nat, forall u8: nat, fst (F u1 u2  u3  u4  u5  u6  u7  u8).
Proof.
let n := constr:(8) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_263);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_263;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_263: forall (u2: PLAN) (u1: nat) (u3: nat) (u4: nat), (memberT u1 (insIn u2 u3 u4)) = true -> (memberT u1 u2) = false -> u3 = u1.
Proof.
do 4 intro.
apply (all_true_263 F_263);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
