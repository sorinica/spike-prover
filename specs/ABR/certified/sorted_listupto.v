
Require Import sorted_listupto_spec.



Definition type_LF_159 :=  nat -> (Prop * (List.list term)).

Definition F_159 : type_LF_159:= (fun    u1 => ((plus u1 0) = u1, (Term id_plus ((model_nat u1):: (Term id_0 nil)::nil))::(model_nat u1)::nil)).
Definition F_169 : type_LF_159:= (fun     _ => (0 = 0, (Term id_0 nil)::(Term id_0 nil)::nil)).
Definition F_175 : type_LF_159:= (fun    u2 => ((S (plus u2 0)) = (S u2), (Term id_S ((Term id_plus ((model_nat u2):: (Term id_0 nil)::nil))::nil))::(Term id_S ((model_nat u2)::nil))::nil)).
Definition F_180 : type_LF_159:= (fun    u2 => (u2 = u2, (model_nat u2)::(model_nat u2)::nil)).

Definition LF_159 := [F_159, F_169, F_175, F_180].


Function f_159 (u1: nat) {struct u1} : nat :=
 match u1 with
| 0 => 0
| (S u2) => 0
end.

Lemma main_159 : forall F, In F LF_159 -> forall u1, (forall F', In F' LF_159 -> forall e1, less (snd (F' e1)) (snd (F u1)) -> fst (F' e1)) -> fst (F u1).
Proof.
intros F HF u1; case_In HF; intro Hind.

	(* GENERATE on [ 159 ] *)

rename u1 into _u1. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_159 u1). apply f_159_ind.

(* case [ 169 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_169). clear HFabs0.
assert (HFabs0 : fst (F_169 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_169. unfold F_159. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_159. unfold F_169.
auto.


(* case [ 175 ] *)

intros _u1. intro u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_175). clear HFabs0.
assert (HFabs0 : fst (F_175 u2)).
apply Hind. trivial_in 2. unfold snd. unfold F_175. unfold F_159. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_159. unfold F_175.
auto.





	(* TAUTOLOGY on [ 169 ] *)

unfold fst. unfold F_169.
auto.



	(* POSITIVE DECOMPOSITION on [ 175 ] *)

rename u1 into _u2. 
rename _u2 into u2. 
assert (H1 := Hind F_159). 
assert (HFabs1 : fst (F_159 u2)).
apply H1. trivial_in 0. unfold snd. unfold F_159. unfold F_175. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_175. unfold F_159.

unfold fst in HFabs1. unfold F_159 in HFabs1.

repeat (auto || (rewrite HFabs1||  auto)).


	(* TAUTOLOGY on [ 180 ] *)

unfold fst. unfold F_180.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_159 := fun f => exists F, In F LF_159 /\ exists e1, f = F e1.

Theorem all_true_159: forall F, In F LF_159 -> forall u1: nat, fst (F u1).
Proof.
let n := constr:(1) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_159);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_159;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_159: forall (u1: nat), (plus u1 0) = u1.
Proof.
do 1 intro.
apply (all_true_159 F_159);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_182 :=  nat ->  nat -> (Prop * (List.list term)).

Definition F_182 : type_LF_182:= (fun    u1 u2 => ((le u1 u2) = false -> (le u1 u2) = true -> False, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_198 : type_LF_182:= (fun    u2 _ => (true = false -> (le 0 u2) = true -> False, (Term id_true nil)::(Term id_false nil)::(Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_204 : type_LF_182:= (fun    u3 _ => (false = false -> (le (S u3) 0) = true -> False, (Term id_false nil)::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_210 : type_LF_182:= (fun    u3 u4 => ((le u3 u4) = false -> (le (S u3) (S u4)) = true -> False, (Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_S ((model_nat u4)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_211 : type_LF_182:= (fun    u3 _ => ((le (S u3) 0) = true -> False, (Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_217 : type_LF_182:= (fun     _ _ => (false = true -> False, (Term id_false nil)::(Term id_true nil)::nil)).

Definition LF_182 := [F_182, F_198, F_204, F_210, F_211, F_217].


Function f_182 (u1: nat) (u2: nat) {struct u1} : bool :=
 match u1, u2 with
| 0, _ => true
| (S u3), 0 => true
| (S u3), (S u4) => true
end.

Lemma main_182 : forall F, In F LF_182 -> forall u1, forall u2, (forall F', In F' LF_182 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 182 ] *)

rename u1 into _u1. rename u2 into _u2. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_182 u1 u2). apply f_182_ind.

(* case [ 198 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_198). clear HFabs0.
assert (HFabs0 : fst (F_198 _u2 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_198. unfold F_182. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_182. unfold F_198.
auto.


(* case [ 204 ] *)

intros _u1 _u2. intro u3.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_204). clear HFabs0.
assert (HFabs0 : fst (F_204 u3 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_204. unfold F_182. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_182. unfold F_204.
auto.


(* case [ 210 ] *)

intros _u1 _u2. intro u3.  intro eq_1. intro u4.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_210). clear HFabs0.
assert (HFabs0 : fst (F_210 u3 u4)).
apply Hind. trivial_in 3. unfold snd. unfold F_210. unfold F_182. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_182. unfold F_210.
auto.





	(* NEGATIVE CLASH on [ 198 ] *)

unfold fst. unfold F_198. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 204 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (H := Hind F_211). 
assert (HFabs0 : fst (F_211 u3 0)).
apply H. trivial_in 4. unfold snd. unfold F_211. unfold F_204. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_204. unfold F_211.

unfold fst in HFabs0. unfold F_211 in HFabs0.
auto.



	(* REWRITING on [ 210 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_182). clear Hind.
assert (HFabs1 : fst (F_182 u3 u4)).
apply Res. trivial_in 0. unfold snd. unfold F_182. unfold F_210. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_210. unfold fst in HFabs1. unfold F_182 in HFabs1.   
pattern u3, u4. simpl (le _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 211 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (Res := Hind F_217). clear Hind.
assert (HFabs1 : fst (F_217 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_217. unfold F_211. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_211. unfold fst in HFabs1. unfold F_217 in HFabs1.   
pattern u3. simpl (le _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE CLASH on [ 217 ] *)

unfold fst. unfold F_217. intros. try discriminate.



Qed.



(* the set of all formula instances from the proof *)
Definition S_182 := fun f => exists F, In F LF_182 /\ exists e1, exists e2, f = F e1 e2.

Theorem all_true_182: forall F, In F LF_182 -> forall u1: nat, forall u2: nat, fst (F u1  u2).
Proof.
let n := constr:(2) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_182);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_182;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_182: forall (u1: nat) (u2: nat), (le u1 u2) = false -> (le u1 u2) = true -> False.
Proof.
do 2 intro.
apply (all_true_182 F_182);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_222 :=  PLAN ->  OBJ ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_222 : type_LF_222:= (fun  u2 u1  _ _ _ => ((sortedT (Cons u1 u2)) = true -> (sortedT u2) = true, (Term id_sortedT ((Term id_Cons ((model_OBJ u1):: (model_PLAN u2)::nil))::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u2)::nil))::(Term id_true nil)::nil)).
Definition F_243 : type_LF_222:= (fun  u7  _ u3 u4 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (sortedT (Cons (C u3 u6) u7)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_249 : type_LF_222:= (fun  u7  _ u3 u4 u6 => (false = true -> (le u3 u4) = false -> (sortedT (Cons (C u3 u6) u7)) = true, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_237 : type_LF_222:= (fun   _  _  _ _ _ => (true = true -> (sortedT Nil) = true, (Term id_true nil)::(Term id_true nil)::(Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_250 : type_LF_222:= (fun   _  _  _ _ _ => ((sortedT Nil) = true, (Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_253 : type_LF_222:= (fun   _  _  _ _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).

Definition LF_222 := [F_222, F_243, F_249, F_237, F_250, F_253].


Function f_222 (u2: PLAN) (u1: OBJ) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons (C u3 u6) u7), (C u4 u5) => true
end.

Lemma main_222 : forall F, In F LF_222 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_222 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 222 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_222 u2 u1). apply f_222_ind.

(* case [ 237 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_237). clear HFabs0.
assert (HFabs0 : fst (F_237 Nil (C 0 0 ) 0 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_237. unfold F_222. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_222. unfold F_237.
auto.



intros _u2 _u1. intro u3. intro u6. intro u7.  intro eq_1. intro u4. intro u5.  intro eq_2.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 243 ] *)

assert (Hind := HFabs0 F_243). clear HFabs0.
assert (HFabs0 : fst (F_243 u7 (C 0 0 ) u3 u4 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_243. unfold F_222. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_222. unfold F_243. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 249 ] *)

assert (Hind := HFabs0 F_249). clear HFabs0.
assert (HFabs0 : fst (F_249 u7 (C 0 0 ) u3 u4 u6)).
apply Hind. trivial_in 2. unfold snd. unfold F_249. unfold F_222. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_222. unfold F_249. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* TAUTOLOGY on [ 243 ] *)

unfold fst. unfold F_243.
auto.



	(* NEGATIVE CLASH on [ 249 ] *)

unfold fst. unfold F_249. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 237 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (H := Hind F_250). 
assert (HFabs0 : fst (F_250 Nil (C 0 0 ) 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_250. unfold F_237. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_237. unfold F_250.

unfold fst in HFabs0. unfold F_250 in HFabs0.
auto.



	(* REWRITING on [ 250 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (Res := Hind F_253). clear Hind.
assert (HFabs1 : fst (F_253 Nil (C 0 0 ) 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_253. unfold F_250. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_250. unfold fst in HFabs1. unfold F_253 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 253 ] *)

unfold fst. unfold F_253.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_222 := fun f => exists F, In F LF_222 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_222: forall F, In F LF_222 -> forall u1: PLAN, forall u2: OBJ, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2 u3  u4  u5).
Proof.
let n := constr:(5) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_222);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_222;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_222: forall (u2: PLAN) (u1: OBJ), (sortedT (Cons u1 u2)) = true -> (sortedT u2) = true.
Proof.
do 2 intro.
apply (all_true_222 F_222);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_254 :=  PLAN ->  OBJ ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_254 : type_LF_254:= (fun  u2 u1  _ _ _ _ => ((sortedT (Cons u1 u2)) = true -> (le (timel u2) (time u1)) = true, (Term id_sortedT ((Term id_Cons ((model_OBJ u1):: (model_PLAN u2)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u2)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_282 : type_LF_254:= (fun  u7  _ u3 u4 u5 u6 => (false = true -> (le u3 u4) = false -> (le (timel (Cons (C u3 u6) u7)) (time (C u4 u5))) = true, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_270 : type_LF_254:= (fun   _ u1  _ _ _ _ => (true = true -> (le (timel Nil) (time u1)) = true, (Term id_true nil)::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_276 : type_LF_254:= (fun  u7  _ u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (timel (Cons (C u3 u6) u7)) (time (C u4 u5))) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_283 : type_LF_254:= (fun   _ u1  _ _ _ _ => ((le (timel Nil) (time u1)) = true, (Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_286 : type_LF_254:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (timel (Cons (C u3 u6) u7)) u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_289 : type_LF_254:= (fun   _ u1  _ _ _ _ => ((le 0 (time u1)) = true, (Term id_le ((Term id_0 nil):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_295 : type_LF_254:= (fun   _  _  _ _ _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).
Definition F_292 : type_LF_254:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (time (C u3 u6)) u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u3):: (model_nat u6)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_298 : type_LF_254:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le u3 u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::nil)).

Definition LF_254 := [F_254, F_282, F_270, F_276, F_283, F_286, F_289, F_295, F_292, F_298].


Function f_254 (u2: PLAN) (u1: OBJ) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons (C u3 u6) u7), (C u4 u5) => true
end.

Lemma main_254 : forall F, In F LF_254 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, (forall F', In F' LF_254 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, less (snd (F' e1 e2 e3 e4 e5 e6)) (snd (F u1 u2 u3 u4 u5 u6)) -> fst (F' e1 e2 e3 e4 e5 e6)) -> fst (F u1 u2 u3 u4 u5 u6).
Proof.
intros F HF u1 u2 u3 u4 u5 u6; case_In HF; intro Hind.

	(* GENERATE on [ 254 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_254 u2 u1). apply f_254_ind.

(* case [ 270 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_270). clear HFabs0.
assert (HFabs0 : fst (F_270 Nil _u1 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_270. unfold F_254. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_254. unfold F_270.
auto.



intros _u2 _u1. intro u3. intro u6. intro u7.  intro eq_1. intro u4. intro u5.  intro eq_2.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 276 ] *)

assert (Hind := HFabs0 F_276). clear HFabs0.
assert (HFabs0 : fst (F_276 u7 (C 0 0 ) u3 u4 u5 u6)).
apply Hind. trivial_in 3. unfold snd. unfold F_276. unfold F_254. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_254. unfold F_276. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 282 ] *)

assert (Hind := HFabs0 F_282). clear HFabs0.
assert (HFabs0 : fst (F_282 u7 (C 0 0 ) u3 u4 u5 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_282. unfold F_254. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_254. unfold F_282. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 282 ] *)

unfold fst. unfold F_282. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 270 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (H := Hind F_283). 
assert (HFabs0 : fst (F_283 Nil u1 0 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_283. unfold F_270. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_270. unfold F_283.

unfold fst in HFabs0. unfold F_283 in HFabs0.
auto.



	(* REWRITING on [ 276 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_286). clear Hind.
assert (HFabs1 : fst (F_286 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 5. unfold snd. unfold F_286. unfold F_276. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_276. unfold fst in HFabs1. unfold F_286 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 283 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (Res := Hind F_289). clear Hind.
assert (HFabs1 : fst (F_289 Nil u1 0 0 0 0)).
apply Res. trivial_in 6. unfold snd. unfold F_289. unfold F_283. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_283. unfold fst in HFabs1. unfold F_289 in HFabs1.    simpl. auto.



	(* REWRITING on [ 286 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_292). clear Hind.
assert (HFabs1 : fst (F_292 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 8. unfold snd. unfold F_292. unfold F_286. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_286. unfold fst in HFabs1. unfold F_292 in HFabs1.   
pattern (C u3 u6), u7. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 289 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (Res := Hind F_295). clear Hind.
assert (HFabs1 : fst (F_295 Nil (C 0 0 ) 0 0 0 0)).
apply Res. trivial_in 7. unfold snd. unfold F_295. unfold F_289. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_289. unfold fst in HFabs1. unfold F_295 in HFabs1.   
pattern (time u1). simpl (le _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 295 ] *)

unfold fst. unfold F_295.
auto.



	(* REWRITING on [ 292 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_298). clear Hind.
assert (HFabs1 : fst (F_298 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 9. unfold snd. unfold F_298. unfold F_292. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_292. unfold fst in HFabs1. unfold F_298 in HFabs1.   
pattern u3, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 298 ] *)

unfold fst. unfold F_298.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_254 := fun f => exists F, In F LF_254 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, f = F e1 e2 e3 e4 e5 e6.

Theorem all_true_254: forall F, In F LF_254 -> forall u1: PLAN, forall u2: OBJ, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, fst (F u1 u2 u3  u4  u5  u6).
Proof.
let n := constr:(6) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_254);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_254;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_254: forall (u2: PLAN) (u1: OBJ), (sortedT (Cons u1 u2)) = true -> (le (timel u2) (time u1)) = true.
Proof.
do 2 intro.
apply (all_true_254 F_254);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_299 :=  PLAN ->  nat ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_299 : type_LF_299:= (fun   u1 u2 _ _ _ _ => ((sortedT u1) = true -> (sortedT (listUpTo u1 u2)) = true, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_listUpTo ((model_PLAN u1):: (model_nat u2)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_330 : type_LF_299:= (fun    _  _ _ _ _ _ => ((sortedT Nil) = true -> (sortedT Nil) = true, (Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_336 : type_LF_299:= (fun   u6 u2 u3 u5 _ _ => ((sortedT (Cons (C u3 u5) u6)) = true -> (le u3 u2) = true -> (sortedT (Cons (C u3 u5) Nil)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_345 : type_LF_299:= (fun   u6 u2 u3 u5 _ _ => ((sortedT (Cons (C u3 u5) u6)) = true -> (le u3 u2) = true -> true = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_true nil)::nil)).
Definition F_342 : type_LF_299:= (fun   u6 u2 u3 u5 _ _ => ((sortedT (Cons (C u3 u5) u6)) = true -> (le u3 u2) = false -> (sortedT (Cons (C u3 u5) (listUpTo u6 u2))) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_listUpTo ((model_PLAN u6):: (model_nat u2)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_367 : type_LF_299:= (fun   u6 u2 u3 u5 _ _ => ((le u3 u2) = false -> (sortedT u6) = true -> (le (timel u6) (time (C u3 u5))) = true -> (sortedT (Cons (C u3 u5) (listUpTo u6 u2))) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (Term id_time ((Term id_C ((model_nat u3):: (model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_listUpTo ((model_PLAN u6):: (model_nat u2)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_370 : type_LF_299:= (fun   u6 u2 u3 u5 _ _ => ((le u3 u2) = false -> (sortedT u6) = true -> (le (timel u6) u3) = true -> (sortedT (Cons (C u3 u5) (listUpTo u6 u2))) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_listUpTo ((model_PLAN u6):: (model_nat u2)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_402 : type_LF_299:= (fun    _ u2 u3 u5 _ _ => ((le u3 u2) = false -> (sortedT Nil) = true -> (le (timel Nil) u3) = true -> (sortedT (Cons (C u3 u5) Nil)) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_417 : type_LF_299:= (fun    _ u2 u3 _ _ _ => ((le u3 u2) = false -> (sortedT Nil) = true -> (le (timel Nil) u3) = true -> true = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_true nil)::nil)).
Definition F_408 : type_LF_299:= (fun   u10 u2 u3 u5 u7 u9 => ((le u3 u2) = false -> (sortedT (Cons (C u7 u9) u10)) = true -> (le (timel (Cons (C u7 u9) u10)) u3) = true -> (le u7 u2) = true -> (sortedT (Cons (C u3 u5) (Cons (C u7 u9) Nil))) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (Term id_Nil nil)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_414 : type_LF_299:= (fun   u10 u2 u3 u5 u7 u9 => ((le u3 u2) = false -> (sortedT (Cons (C u7 u9) u10)) = true -> (le (timel (Cons (C u7 u9) u10)) u3) = true -> (le u7 u2) = false -> (sortedT (Cons (C u3 u5) (Cons (C u7 u9) (listUpTo u10 u2)))) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (Term id_listUpTo ((model_PLAN u10):: (model_nat u2)::nil))::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_420 : type_LF_299:= (fun   u10 u2 u3 u5 u7 u9 => ((le u3 u2) = false -> (sortedT (Cons (C u7 u9) u10)) = true -> (le (time (C u7 u9)) u3) = true -> (le u7 u2) = true -> (sortedT (Cons (C u3 u5) (Cons (C u7 u9) Nil))) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u7):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (Term id_Nil nil)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_423 : type_LF_299:= (fun   u10 u2 u3 u5 u7 u9 => ((le u3 u2) = false -> (sortedT (Cons (C u7 u9) u10)) = true -> (le (time (C u7 u9)) u3) = true -> (le u7 u2) = false -> (sortedT (Cons (C u3 u5) (Cons (C u7 u9) (listUpTo u10 u2)))) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u7):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (Term id_listUpTo ((model_PLAN u10):: (model_nat u2)::nil))::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_426 : type_LF_299:= (fun   u10 u2 u3 u5 u7 u9 => ((le u3 u2) = false -> (sortedT (Cons (C u7 u9) u10)) = true -> (le u7 u3) = true -> (le u7 u2) = true -> (sortedT (Cons (C u3 u5) (Cons (C u7 u9) Nil))) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (Term id_Nil nil)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_451 : type_LF_299:= (fun   u10 u2 u3 u5 u7 u9 => ((le u3 u2) = false -> (le u7 u3) = true -> (le u7 u2) = true -> (sortedT u10) = true -> (le (timel u10) (time (C u7 u9))) = true -> (sortedT (Cons (C u3 u5) (Cons (C u7 u9) Nil))) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u10)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u10)::nil)):: (Term id_time ((Term id_C ((model_nat u7):: (model_nat u9)::nil))::nil))::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (Term id_Nil nil)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_429 : type_LF_299:= (fun   u10 u2 u3 u5 u7 u9 => ((le u3 u2) = false -> (sortedT (Cons (C u7 u9) u10)) = true -> (le u7 u3) = true -> (le u7 u2) = false -> (sortedT (Cons (C u3 u5) (Cons (C u7 u9) (listUpTo u10 u2)))) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (Term id_listUpTo ((model_PLAN u10):: (model_nat u2)::nil))::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_476 : type_LF_299:= (fun   u10 u2 u3 u5 u7 u9 => ((le u3 u2) = false -> (le u7 u3) = true -> (le u7 u2) = false -> (sortedT u10) = true -> (le (timel u10) (time (C u7 u9))) = true -> (sortedT (Cons (C u3 u5) (Cons (C u7 u9) (listUpTo u10 u2)))) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u10)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u10)::nil)):: (Term id_time ((Term id_C ((model_nat u7):: (model_nat u9)::nil))::nil))::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (Term id_listUpTo ((model_PLAN u10):: (model_nat u2)::nil))::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_454 : type_LF_299:= (fun   u10 u2 u3 u5 u7 u9 => ((le u3 u2) = false -> (le u7 u3) = true -> (le u7 u2) = true -> (sortedT u10) = true -> (le (timel u10) u7) = true -> (sortedT (Cons (C u3 u5) (Cons (C u7 u9) Nil))) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u10)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u10)::nil)):: (model_nat u7)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (Term id_Nil nil)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_532 : type_LF_299:= (fun   u10 u2 u3 u7 u9 _ => ((le u3 u2) = false -> (le u7 u3) = true -> (le u7 u2) = true -> (sortedT u10) = true -> (le (timel u10) u7) = true -> (le u7 u3) = true -> (sortedT (Cons (C u7 u9) Nil)) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u10)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u10)::nil)):: (model_nat u7)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_539 : type_LF_299:= (fun   u10 u2 u3 u7 _ _ => ((le u3 u2) = false -> (le u7 u3) = true -> (le u7 u2) = true -> (sortedT u10) = true -> (le (timel u10) u7) = true -> (le u7 u3) = true -> true = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u10)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u10)::nil)):: (model_nat u7)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_true nil)::nil)).
Definition F_536 : type_LF_299:= (fun   u10 u2 u3 u7 _ _ => ((le u3 u2) = false -> (le u7 u3) = true -> (le u7 u2) = true -> (sortedT u10) = true -> (le (timel u10) u7) = true -> (le u7 u3) = false -> false = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u10)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u10)::nil)):: (model_nat u7)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_false nil)::(Term id_true nil)::nil)).
Definition F_479 : type_LF_299:= (fun   u10 u2 u3 u5 u7 u9 => ((le u3 u2) = false -> (le u7 u3) = true -> (le u7 u2) = false -> (sortedT u10) = true -> (le (timel u10) u7) = true -> (sortedT (Cons (C u3 u5) (Cons (C u7 u9) (listUpTo u10 u2)))) = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u10)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u10)::nil)):: (model_nat u7)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u7):: (model_nat u9)::nil)):: (Term id_listUpTo ((model_PLAN u10):: (model_nat u2)::nil))::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_578 : type_LF_299:= (fun   u10 u2 u3 u7 _ _ => ((le u3 u2) = false -> (le u7 u3) = true -> (le u7 u2) = false -> (sortedT u10) = true -> (le (timel u10) u7) = true -> (le u7 u3) = false -> false = true, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u10)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u10)::nil)):: (model_nat u7)::nil))::(Term id_true nil)::(Term id_le ((model_nat u7):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_false nil)::(Term id_true nil)::nil)).

Definition LF_299 := [F_299, F_330, F_336, F_345, F_342, F_367, F_370, F_402, F_417, F_408, F_414, F_420, F_423, F_426, F_451, F_429, F_476, F_454, F_532, F_539, F_536, F_479, F_578].


Function f_299 (u1: PLAN) (u2: nat) {struct u1} : PLAN :=
 match u1, u2 with
| Nil, _ => Nil
| (Cons (C u3 u5) u6), _ => Nil
end.

Function f_370 (u6: PLAN) (u2: nat) {struct u6} : PLAN :=
 match u6, u2 with
| Nil, _ => Nil
| (Cons (C u7 u9) u10), _ => Nil
end.

Lemma main_299 : forall F, In F LF_299 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, (forall F', In F' LF_299 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, less (snd (F' e1 e2 e3 e4 e5 e6)) (snd (F u1 u2 u3 u4 u5 u6)) -> fst (F' e1 e2 e3 e4 e5 e6)) -> fst (F u1 u2 u3 u4 u5 u6).
Proof.
intros F HF u1 u2 u3 u4 u5 u6; case_In HF; intro Hind.

	(* GENERATE on [ 299 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_299 u1 u2). apply f_299_ind.

(* case [ 330 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_330). clear HFabs0.
assert (HFabs0 : fst (F_330 Nil 0 0 0 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_330. unfold F_299. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_299. unfold F_330.
auto.



intros _u1 _u2. intro u3. intro u5. intro u6.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
case_eq (le u3 _u2); [intro H | intro H].

(* case [ 336 ] *)

assert (Hind := HFabs0 F_336). clear HFabs0.
assert (HFabs0 : fst (F_336 u6 _u2 u3 u5 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_336. unfold F_299. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_299. unfold F_336. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 342 ] *)

assert (Hind := HFabs0 F_342). clear HFabs0.
assert (HFabs0 : fst (F_342 u6 _u2 u3 u5 0 0)).
apply Hind. trivial_in 4. unfold snd. unfold F_342. unfold F_299. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_299. unfold F_342. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* TAUTOLOGY on [ 330 ] *)

unfold fst. unfold F_330.
auto.



	(* REWRITING on [ 336 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_345). clear Hind.
assert (HFabs1 : fst (F_345 u6 u2 u3 u5 0 0)).
apply Res. trivial_in 3. unfold snd. unfold F_345. unfold F_336. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_336. unfold fst in HFabs1. unfold F_345 in HFabs1.   
pattern (C u3 u5). simpl (sortedT _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 345 ] *)

unfold fst. unfold F_345.
auto.



	(* AUGMENTATION on [ 342 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
assert (H := Hind F_367). clear Hind.
assert (HFabs0: fst (F_367 u6 u2 u3 u5 0 0)).
apply H. trivial_in 5. unfold snd. unfold F_342. unfold F_367. rewrite_model. abstract solve_rpo_mul.

unfold fst. unfold F_342.

specialize true_254 with (u1 := (C u3 u5)) (u2 := u6).
specialize true_222 with (u1 := (C u3 u5)) (u2 := u6). auto.




	(* REWRITING on [ 367 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_370). clear Hind.
assert (HFabs1 : fst (F_370 u6 u2 u3 u5 0 0)).
apply Res. trivial_in 6. unfold snd. unfold F_370. unfold F_367. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_367. unfold fst in HFabs1. unfold F_370 in HFabs1.   
pattern u3, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* GENERATE on [ 370 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 

revert Hind.

pattern u6, u2, (f_370 u6 u2). apply f_370_ind.

(* case [ 402 ] *)

intros _u6 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_402). clear HFabs0.
assert (HFabs0 : fst (F_402 Nil _u2 u3 u5 0 0)).
apply Hind. trivial_in 7. unfold snd. unfold F_402. unfold F_370. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_370. unfold F_402.
auto.



intros _u6 _u2. intro u7. intro u9. intro u10.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
case_eq (le u7 _u2); [intro H | intro H].

(* case [ 408 ] *)

assert (Hind := HFabs0 F_408). clear HFabs0.
assert (HFabs0 : fst (F_408 u10 _u2 u3 u5 u7 u9)).
apply Hind. trivial_in 9. unfold snd. unfold F_408. unfold F_370. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_370. unfold F_408. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 414 ] *)

assert (Hind := HFabs0 F_414). clear HFabs0.
assert (HFabs0 : fst (F_414 u10 _u2 u3 u5 u7 u9)).
apply Hind. trivial_in 10. unfold snd. unfold F_414. unfold F_370. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_370. unfold F_414. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* REWRITING on [ 402 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_417). clear Hind.
assert (HFabs1 : fst (F_417 Nil u2 u3 0 0 0)).
apply Res. trivial_in 8. unfold snd. unfold F_417. unfold F_402. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_402. unfold fst in HFabs1. unfold F_417 in HFabs1.   
pattern (C u3 u5). simpl (sortedT _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 417 ] *)

unfold fst. unfold F_417.
auto.



	(* REWRITING on [ 408 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u7. rename u6 into _u9. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u7 into u7. rename _u9 into u9. 
assert (Res := Hind F_420). clear Hind.
assert (HFabs1 : fst (F_420 u10 u2 u3 u5 u7 u9)).
apply Res. trivial_in 11. unfold snd. unfold F_420. unfold F_408. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_408. unfold fst in HFabs1. unfold F_420 in HFabs1.   
pattern (C u7 u9), u10. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 414 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u7. rename u6 into _u9. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u7 into u7. rename _u9 into u9. 
assert (Res := Hind F_423). clear Hind.
assert (HFabs1 : fst (F_423 u10 u2 u3 u5 u7 u9)).
apply Res. trivial_in 12. unfold snd. unfold F_423. unfold F_414. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_414. unfold fst in HFabs1. unfold F_423 in HFabs1.   
pattern (C u7 u9), u10. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 420 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u7. rename u6 into _u9. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u7 into u7. rename _u9 into u9. 
assert (Res := Hind F_426). clear Hind.
assert (HFabs1 : fst (F_426 u10 u2 u3 u5 u7 u9)).
apply Res. trivial_in 13. unfold snd. unfold F_426. unfold F_420. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_420. unfold fst in HFabs1. unfold F_426 in HFabs1.   
pattern u7, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 423 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u7. rename u6 into _u9. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u7 into u7. rename _u9 into u9. 
assert (Res := Hind F_429). clear Hind.
assert (HFabs1 : fst (F_429 u10 u2 u3 u5 u7 u9)).
apply Res. trivial_in 15. unfold snd. unfold F_429. unfold F_423. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_423. unfold fst in HFabs1. unfold F_429 in HFabs1.   
pattern u7, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* AUGMENTATION on [ 426 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u7. rename u6 into _u9. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u7 into u7. rename _u9 into u9. 
assert (H := Hind F_451). clear Hind.
assert (HFabs0: fst (F_451 u10 u2 u3 u5 u7 u9)).
apply H. trivial_in 14. unfold snd. unfold F_426. unfold F_451. rewrite_model. abstract solve_rpo_mul.

unfold fst. unfold F_426.

specialize true_254 with (u1 := (C u7 u9)) (u2 := u10).
specialize true_222 with (u1 := (C u7 u9)) (u2 := u10). auto.




	(* REWRITING on [ 451 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u7. rename u6 into _u9. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u7 into u7. rename _u9 into u9. 
assert (Res := Hind F_454). clear Hind.
assert (HFabs1 : fst (F_454 u10 u2 u3 u5 u7 u9)).
apply Res. trivial_in 17. unfold snd. unfold F_454. unfold F_451. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_451. unfold fst in HFabs1. unfold F_454 in HFabs1.   
pattern u7, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* AUGMENTATION on [ 429 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u7. rename u6 into _u9. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u7 into u7. rename _u9 into u9. 
assert (H := Hind F_476). clear Hind.
assert (HFabs0: fst (F_476 u10 u2 u3 u5 u7 u9)).
apply H. trivial_in 16. unfold snd. unfold F_429. unfold F_476. rewrite_model. abstract solve_rpo_mul.

unfold fst. unfold F_429.

specialize true_254 with (u1 := (C u7 u9)) (u2 := u10).
specialize true_222 with (u1 := (C u7 u9)) (u2 := u10). auto.




	(* REWRITING on [ 476 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u7. rename u6 into _u9. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u7 into u7. rename _u9 into u9. 
assert (Res := Hind F_479). clear Hind.
assert (HFabs1 : fst (F_479 u10 u2 u3 u5 u7 u9)).
apply Res. trivial_in 21. unfold snd. unfold F_479. unfold F_476. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_476. unfold fst in HFabs1. unfold F_479 in HFabs1.   
pattern u7, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 454 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u7. rename u6 into _u9. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u7 into u7. rename _u9 into u9. 
assert (H: ((le u7 u3) = true) \/ ((le u7 u3) = false)). 

destruct ((le u7 u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 109 ] *)

assert (H1 := Hind F_532). clear Hind.
assert (HFabs0 : fst (F_532 u10 u2 u3 u7 u9 0)).
apply H1. trivial_in 18. unfold snd. unfold F_532. unfold F_454. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_454. unfold F_532. unfold fst in HFabs0. unfold F_532 in HFabs0. simpl in HFabs0. 
pattern u7.
pattern u3.
pattern u5.
pattern u9.
pattern Nil.
simpl (sortedT _). cbv beta. try unfold sortedT. try rewrite H. try rewrite H0. try unfold sortedT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 110 ] *)

assert (H1 := Hind F_536). clear Hind.
assert (HFabs0 : fst (F_536 u10 u2 u3 u7 0 0)).
apply H1. trivial_in 20. unfold snd. unfold F_536. unfold F_454. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_454. unfold F_536. unfold fst in HFabs0. unfold F_536 in HFabs0. simpl in HFabs0. 
pattern u7.
pattern u3.
pattern u5.
pattern u9.
pattern Nil.
simpl (sortedT _). cbv beta. try unfold sortedT. try rewrite H. try rewrite H0. try unfold sortedT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 532 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u7. rename u5 into _u9. rename u6 into d_u6. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u7 into u7. rename _u9 into u9. 
assert (Res := Hind F_539). clear Hind.
assert (HFabs1 : fst (F_539 u10 u2 u3 u7 0 0)).
apply Res. trivial_in 19. unfold snd. unfold F_539. unfold F_532. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_532. unfold fst in HFabs1. unfold F_539 in HFabs1.   
pattern (C u7 u9). simpl (sortedT _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 539 ] *)

unfold fst. unfold F_539.
auto.



	(* SUBSUMPTION on [ 536 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u7. rename u5 into d_u5. rename u6 into d_u6. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u7 into u7. 
unfold fst. unfold F_536. specialize true_182 with (u1 := u7) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 479 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u7. rename u6 into _u9. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u7 into u7. rename _u9 into u9. 
assert (H: ((le u7 u3) = true) \/ ((le u7 u3) = false)). 

destruct ((le u7 u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 109 ] *)

assert (H1 := Hind F_370). clear Hind.
assert (HFabs0 : fst (F_370 u10 u2 u7 u9 0 0)).
apply H1. trivial_in 6. unfold snd. unfold F_370. unfold F_479. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_479. unfold F_370. unfold fst in HFabs0. unfold F_370 in HFabs0. simpl in HFabs0. 
pattern u7.
pattern u3.
pattern u5.
pattern u9.
pattern (listUpTo u10 u2).
simpl (sortedT _). cbv beta. try unfold sortedT. try rewrite H. try rewrite H0. try unfold sortedT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 110 ] *)

assert (H1 := Hind F_578). clear Hind.
assert (HFabs0 : fst (F_578 u10 u2 u3 u7 0 0)).
apply H1. trivial_in 22. unfold snd. unfold F_578. unfold F_479. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_479. unfold F_578. unfold fst in HFabs0. unfold F_578 in HFabs0. simpl in HFabs0. 
pattern u7.
pattern u3.
pattern u5.
pattern u9.
pattern (listUpTo u10 u2).
simpl (sortedT _). cbv beta. try unfold sortedT. try rewrite H. try rewrite H0. try unfold sortedT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* SUBSUMPTION on [ 578 ] *)

rename u1 into _u10. rename u2 into _u2. rename u3 into _u3. rename u4 into _u7. rename u5 into d_u5. rename u6 into d_u6. 
rename _u10 into u10. rename _u2 into u2. rename _u3 into u3. rename _u7 into u7. 
unfold fst. unfold F_578. specialize true_182 with (u1 := u7) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_299 := fun f => exists F, In F LF_299 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, f = F e1 e2 e3 e4 e5 e6.

Theorem all_true_299: forall F, In F LF_299 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, fst (F u1 u2  u3  u4  u5  u6).
Proof.
let n := constr:(6) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_299);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_299;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_299: forall (u1: PLAN) (u2: nat), (sortedT u1) = true -> (sortedT (listUpTo u1 u2)) = true.
Proof.
do 2 intro.
apply (all_true_299 F_299);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
