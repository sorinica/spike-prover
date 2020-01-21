
Require Import progat_insat_spec.



Definition type_LF_159 :=  nat ->  nat -> (Prop * (List.list term)).

Definition F_159 : type_LF_159:= (fun    u1 u2 => ((le u1 u2) = false -> (le u1 u2) = true -> False, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_175 : type_LF_159:= (fun    u2 _ => (true = false -> (le 0 u2) = true -> False, (Term id_true nil)::(Term id_false nil)::(Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_181 : type_LF_159:= (fun    u3 _ => (false = false -> (le (S u3) 0) = true -> False, (Term id_false nil)::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_187 : type_LF_159:= (fun    u3 u4 => ((le u3 u4) = false -> (le (S u3) (S u4)) = true -> False, (Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_S ((model_nat u4)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_188 : type_LF_159:= (fun    u3 _ => ((le (S u3) 0) = true -> False, (Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_194 : type_LF_159:= (fun     _ _ => (false = true -> False, (Term id_false nil)::(Term id_true nil)::nil)).

Definition LF_159 := [F_159, F_175, F_181, F_187, F_188, F_194].


Function f_159 (u1: nat) (u2: nat) {struct u1} : bool :=
 match u1, u2 with
| 0, _ => true
| (S u3), 0 => true
| (S u3), (S u4) => true
end.


Hypothesis true_154: forall u1 u2 u3, (le u1 u2) = true -> (le u1 u3) = false -> (le u3 u2) = false -> False.

Lemma main_159 : forall F, In F LF_159 -> forall u1, forall u2, (forall F', In F' LF_159 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 159 ] *)

rename u1 into _u1. rename u2 into _u2. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_159 u1 u2). apply f_159_ind.

(* case [ 175 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_175). clear HFabs0.
assert (HFabs0 : fst (F_175 _u2 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_175. unfold F_159. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_159. unfold F_175.
auto.


(* case [ 181 ] *)

intros _u1 _u2. intro u3.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_181). clear HFabs0.
assert (HFabs0 : fst (F_181 u3 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_181. unfold F_159. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_159. unfold F_181.
auto.


(* case [ 187 ] *)

intros _u1 _u2. intro u3.  intro eq_1. intro u4.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_187). clear HFabs0.
assert (HFabs0 : fst (F_187 u3 u4)).
apply Hind. trivial_in 3. unfold snd. unfold F_187. unfold F_159. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_159. unfold F_187.
auto.





	(* NEGATIVE CLASH on [ 175 ] *)

unfold fst. unfold F_175. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 181 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (H := Hind F_188). 
assert (HFabs0 : fst (F_188 u3 0)).
apply H. trivial_in 4. unfold snd. unfold F_188. unfold F_181. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_181. unfold F_188.

unfold fst in HFabs0. unfold F_188 in HFabs0.
auto.



	(* REWRITING on [ 187 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_159). clear Hind.
assert (HFabs1 : fst (F_159 u3 u4)).
apply Res. trivial_in 0. unfold snd. unfold F_159. unfold F_187. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_187. unfold fst in HFabs1. unfold F_159 in HFabs1.   
pattern u3, u4. simpl (le _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 188 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (Res := Hind F_194). clear Hind.
assert (HFabs1 : fst (F_194 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_194. unfold F_188. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_188. unfold fst in HFabs1. unfold F_194 in HFabs1.   
pattern u3. simpl (le _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE CLASH on [ 194 ] *)

unfold fst. unfold F_194. intros. try discriminate.



Qed.



(* the set of all formula instances from the proof *)
Definition S_159 := fun f => exists F, In F LF_159 /\ exists e1, exists e2, f = F e1 e2.

Theorem all_true_159: forall F, In F LF_159 -> forall u1: nat, forall u2: nat, fst (F u1  u2).
Proof.
let n := constr:(2) in
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


Theorem true_159: forall (u1: nat) (u2: nat), (le u1 u2) = false -> (le u1 u2) = true -> False.
Proof.
do 2 intro.
apply (all_true_159 F_159);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_199 :=  PLAN ->  OBJ ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_199 : type_LF_199:= (fun  u2 u1  _ _ _ => ((sortedT (Cons u1 u2)) = true -> (sortedT u2) = true, (Term id_sortedT ((Term id_Cons ((model_OBJ u1):: (model_PLAN u2)::nil))::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u2)::nil))::(Term id_true nil)::nil)).
Definition F_220 : type_LF_199:= (fun  u7  _ u3 u4 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (sortedT (Cons (C u3 u6) u7)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_226 : type_LF_199:= (fun  u7  _ u3 u4 u6 => (false = true -> (le u3 u4) = false -> (sortedT (Cons (C u3 u6) u7)) = true, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_214 : type_LF_199:= (fun   _  _  _ _ _ => (true = true -> (sortedT Nil) = true, (Term id_true nil)::(Term id_true nil)::(Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_227 : type_LF_199:= (fun   _  _  _ _ _ => ((sortedT Nil) = true, (Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_230 : type_LF_199:= (fun   _  _  _ _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).

Definition LF_199 := [F_199, F_220, F_226, F_214, F_227, F_230].


Function f_199 (u2: PLAN) (u1: OBJ) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons (C u3 u6) u7), (C u4 u5) => true
end.

Lemma main_199 : forall F, In F LF_199 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_199 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 199 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_199 u2 u1). apply f_199_ind.

(* case [ 214 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_214). clear HFabs0.
assert (HFabs0 : fst (F_214 Nil (C 0 0 ) 0 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_214. unfold F_199. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_199. unfold F_214.
auto.



intros _u2 _u1. intro u3. intro u6. intro u7.  intro eq_1. intro u4. intro u5.  intro eq_2.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 220 ] *)

assert (Hind := HFabs0 F_220). clear HFabs0.
assert (HFabs0 : fst (F_220 u7 (C 0 0 ) u3 u4 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_220. unfold F_199. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_199. unfold F_220. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 226 ] *)

assert (Hind := HFabs0 F_226). clear HFabs0.
assert (HFabs0 : fst (F_226 u7 (C 0 0 ) u3 u4 u6)).
apply Hind. trivial_in 2. unfold snd. unfold F_226. unfold F_199. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_199. unfold F_226. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* TAUTOLOGY on [ 220 ] *)

unfold fst. unfold F_220.
auto.



	(* NEGATIVE CLASH on [ 226 ] *)

unfold fst. unfold F_226. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 214 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (H := Hind F_227). 
assert (HFabs0 : fst (F_227 Nil (C 0 0 ) 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_227. unfold F_214. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_214. unfold F_227.

unfold fst in HFabs0. unfold F_227 in HFabs0.
auto.



	(* REWRITING on [ 227 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (Res := Hind F_230). clear Hind.
assert (HFabs1 : fst (F_230 Nil (C 0 0 ) 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_230. unfold F_227. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_227. unfold fst in HFabs1. unfold F_230 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 230 ] *)

unfold fst. unfold F_230.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_199 := fun f => exists F, In F LF_199 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_199: forall F, In F LF_199 -> forall u1: PLAN, forall u2: OBJ, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2 u3  u4  u5).
Proof.
let n := constr:(5) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_199);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_199;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_199: forall (u2: PLAN) (u1: OBJ), (sortedT (Cons u1 u2)) = true -> (sortedT u2) = true.
Proof.
do 2 intro.
apply (all_true_199 F_199);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_231 :=  PLAN ->  OBJ ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_231 : type_LF_231:= (fun  u2 u1  _ _ _ _ => ((sortedT (Cons u1 u2)) = true -> (le (timel u2) (time u1)) = true, (Term id_sortedT ((Term id_Cons ((model_OBJ u1):: (model_PLAN u2)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u2)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_259 : type_LF_231:= (fun  u7  _ u3 u4 u5 u6 => (false = true -> (le u3 u4) = false -> (le (timel (Cons (C u3 u6) u7)) (time (C u4 u5))) = true, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_247 : type_LF_231:= (fun   _ u1  _ _ _ _ => (true = true -> (le (timel Nil) (time u1)) = true, (Term id_true nil)::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_253 : type_LF_231:= (fun  u7  _ u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (timel (Cons (C u3 u6) u7)) (time (C u4 u5))) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_260 : type_LF_231:= (fun   _ u1  _ _ _ _ => ((le (timel Nil) (time u1)) = true, (Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_263 : type_LF_231:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (timel (Cons (C u3 u6) u7)) u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_266 : type_LF_231:= (fun   _ u1  _ _ _ _ => ((le 0 (time u1)) = true, (Term id_le ((Term id_0 nil):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_272 : type_LF_231:= (fun   _  _  _ _ _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).
Definition F_269 : type_LF_231:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (time (C u3 u6)) u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u3):: (model_nat u6)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_275 : type_LF_231:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le u3 u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::nil)).

Definition LF_231 := [F_231, F_259, F_247, F_253, F_260, F_263, F_266, F_272, F_269, F_275].


Function f_231 (u2: PLAN) (u1: OBJ) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons (C u3 u6) u7), (C u4 u5) => true
end.

Lemma main_231 : forall F, In F LF_231 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, (forall F', In F' LF_231 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, less (snd (F' e1 e2 e3 e4 e5 e6)) (snd (F u1 u2 u3 u4 u5 u6)) -> fst (F' e1 e2 e3 e4 e5 e6)) -> fst (F u1 u2 u3 u4 u5 u6).
Proof.
intros F HF u1 u2 u3 u4 u5 u6; case_In HF; intro Hind.

	(* GENERATE on [ 231 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_231 u2 u1). apply f_231_ind.

(* case [ 247 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_247). clear HFabs0.
assert (HFabs0 : fst (F_247 Nil _u1 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_247. unfold F_231. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_231. unfold F_247.
auto.



intros _u2 _u1. intro u3. intro u6. intro u7.  intro eq_1. intro u4. intro u5.  intro eq_2.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 253 ] *)

assert (Hind := HFabs0 F_253). clear HFabs0.
assert (HFabs0 : fst (F_253 u7 (C 0 0 ) u3 u4 u5 u6)).
apply Hind. trivial_in 3. unfold snd. unfold F_253. unfold F_231. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_231. unfold F_253. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 259 ] *)

assert (Hind := HFabs0 F_259). clear HFabs0.
assert (HFabs0 : fst (F_259 u7 (C 0 0 ) u3 u4 u5 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_259. unfold F_231. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_231. unfold F_259. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 259 ] *)

unfold fst. unfold F_259. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 247 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (H := Hind F_260). 
assert (HFabs0 : fst (F_260 Nil u1 0 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_260. unfold F_247. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_247. unfold F_260.

unfold fst in HFabs0. unfold F_260 in HFabs0.
auto.



	(* REWRITING on [ 253 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_263). clear Hind.
assert (HFabs1 : fst (F_263 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 5. unfold snd. unfold F_263. unfold F_253. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_253. unfold fst in HFabs1. unfold F_263 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 260 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (Res := Hind F_266). clear Hind.
assert (HFabs1 : fst (F_266 Nil u1 0 0 0 0)).
apply Res. trivial_in 6. unfold snd. unfold F_266. unfold F_260. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_260. unfold fst in HFabs1. unfold F_266 in HFabs1.    simpl. auto.



	(* REWRITING on [ 263 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_269). clear Hind.
assert (HFabs1 : fst (F_269 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 8. unfold snd. unfold F_269. unfold F_263. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_263. unfold fst in HFabs1. unfold F_269 in HFabs1.   
pattern (C u3 u6), u7. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 266 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (Res := Hind F_272). clear Hind.
assert (HFabs1 : fst (F_272 Nil (C 0 0 ) 0 0 0 0)).
apply Res. trivial_in 7. unfold snd. unfold F_272. unfold F_266. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_266. unfold fst in HFabs1. unfold F_272 in HFabs1.   
pattern (time u1). simpl (le _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 272 ] *)

unfold fst. unfold F_272.
auto.



	(* REWRITING on [ 269 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_275). clear Hind.
assert (HFabs1 : fst (F_275 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 9. unfold snd. unfold F_275. unfold F_269. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_269. unfold fst in HFabs1. unfold F_275 in HFabs1.   
pattern u3, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 275 ] *)

unfold fst. unfold F_275.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_231 := fun f => exists F, In F LF_231 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, f = F e1 e2 e3 e4 e5 e6.

Theorem all_true_231: forall F, In F LF_231 -> forall u1: PLAN, forall u2: OBJ, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, fst (F u1 u2 u3  u4  u5  u6).
Proof.
let n := constr:(6) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_231);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_231;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_231: forall (u2: PLAN) (u1: OBJ), (sortedT (Cons u1 u2)) = true -> (le (timel u2) (time u1)) = true.
Proof.
do 2 intro.
apply (all_true_231 F_231);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_276 :=  PLAN ->  nat ->  nat ->  nat ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_276 : type_LF_276:= (fun   u1 u2 u3 u4 _ _ _ _ => ((sortedT u1) = true -> (le u2 u3) = false -> (progAt (insAt u1 u2 u4) u3) = (progAt u1 u3), (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((model_PLAN u1):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u1):: (model_nat u3)::nil))::nil)).
Definition F_328 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => (false = true -> (le u2 u3) = false -> (le u5 u6) = false -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = (progAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u3), (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::nil)).
Definition F_310 : type_LF_276:= (fun    _ u2 u3 u4 _ _ _ _ => (true = true -> (le u2 u3) = false -> (progAt (insAt Nil u2 u4) u3) = (progAt Nil u3), (Term id_true nil)::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Nil nil):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((Term id_Nil nil):: (model_nat u3)::nil))::nil)).
Definition F_316 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => (true = true -> (le u2 u3) = false -> (progAt (insAt (Cons (C u6 u7) Nil) u2 u4) u3) = (progAt (Cons (C u6 u7) Nil) u3), (Term id_true nil)::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::nil)).
Definition F_329 : type_LF_276:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = false -> (progAt (insAt Nil u2 u4) u3) = (progAt Nil u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Nil nil):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((Term id_Nil nil):: (model_nat u3)::nil))::nil)).
Definition F_333 : type_LF_276:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = false -> (progAt (insAt Nil u2 u4) u3) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Nil nil):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_0 nil)::nil)).
Definition F_322 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((sortedT (Cons (C u5 u8) u9)) = true -> (le u2 u3) = false -> (le u5 u6) = true -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = (progAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u3), (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::nil)).
Definition F_375 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) (time (C u5 u8))) = true -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = (progAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil))::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::nil)).
Definition F_336 : type_LF_276:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = false -> (progAt (Cons (C u2 u4) Nil) u3) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(Term id_0 nil)::nil)).
Definition F_438 : type_LF_276:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = false -> (le (time (C u2 u4)) u3) = true -> (er (C u2 u4)) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(Term id_0 nil)::nil)).
Definition F_442 : type_LF_276:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = false -> (le (time (C u2 u4)) u3) = false -> (progAt Nil u3) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Nil nil):: (model_nat u3)::nil))::(Term id_0 nil)::nil)).
Definition F_448 : type_LF_276:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = false -> (le (time (C u2 u4)) u3) = false -> 0 = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_0 nil)::(Term id_0 nil)::nil)).
Definition F_445 : type_LF_276:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = false -> (le u2 u3) = true -> (er (C u2 u4)) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(Term id_0 nil)::nil)).
Definition F_451 : type_LF_276:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = false -> (le u2 u3) = true -> u4 = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(Term id_0 nil)::nil)).
Definition F_330 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (progAt (insAt (Cons (C u6 u7) Nil) u2 u4) u3) = (progAt (Cons (C u6 u7) Nil) u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::nil)).
Definition F_495 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le (time (C u6 u7)) u3) = true -> (progAt (insAt (Cons (C u6 u7) Nil) u2 u4) u3) = (er (C u6 u7)), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::nil)).
Definition F_499 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le (time (C u6 u7)) u3) = false -> (progAt (insAt (Cons (C u6 u7) Nil) u2 u4) u3) = (progAt Nil u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((Term id_Nil nil):: (model_nat u3)::nil))::nil)).
Definition F_502 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (progAt (insAt (Cons (C u6 u7) Nil) u2 u4) u3) = (er (C u6 u7)), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::nil)).
Definition F_505 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le (time (C u6 u7)) u3) = false -> (progAt (insAt (Cons (C u6 u7) Nil) u2 u4) u3) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_0 nil)::nil)).
Definition F_378 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = (progAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::nil)).
Definition F_569 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le (time (C u6 u7)) u3) = true -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = (er (C u6 u7)), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::nil)).
Definition F_573 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le (time (C u6 u7)) u3) = false -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = (progAt (Cons (C u5 u8) u9) u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::nil)).
Definition F_576 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = (er (C u6 u7)), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::nil)).
Definition F_579 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = (progAt (Cons (C u5 u8) u9) u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::nil)).
Definition F_648 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le (time (C u5 u8)) u3) = true -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = (er (C u5 u8)), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_er ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil))::nil)).
Definition F_652 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le (time (C u5 u8)) u3) = false -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_655 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = (er (C u5 u8)), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_er ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil))::nil)).
Definition F_658 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_733 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le (time (C u6 u7)) u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) (Cons (C u5 u8) u9))) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil))::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_737 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le (time (C u6 u7)) u2) = false -> (progAt (insAt (Cons (C u5 u8) u9) u2 u4) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_508 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (progAt (insAt (Cons (C u6 u7) Nil) u2 u4) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_817 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le (time (C u6 u7)) u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) Nil)) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_821 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le (time (C u6 u7)) u2) = false -> (progAt (insAt Nil u2 u4) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Nil nil):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_827 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le (time (C u6 u7)) u2) = false -> (progAt (Cons (C u2 u4) Nil) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_830 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = false -> (progAt (Cons (C u2 u4) Nil) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_511 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = false -> (progAt (insAt (Cons (C u6 u7) Nil) u2 u4) u3) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_0 nil)::nil)).
Definition F_926 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = false -> (le (time (C u6 u7)) u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) Nil)) u3) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil))::nil)):: (model_nat u3)::nil))::(Term id_0 nil)::nil)).
Definition F_930 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = false -> (le (time (C u6 u7)) u2) = false -> (progAt (insAt Nil u2 u4) u3) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Nil nil):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_0 nil)::nil)).
Definition F_936 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = false -> (le (time (C u6 u7)) u2) = false -> (progAt (Cons (C u2 u4) Nil) u3) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(Term id_0 nil)::nil)).
Definition F_582 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_1039 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le (time (C u6 u7)) u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) (Cons (C u5 u8) u9))) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil))::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_1043 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le (time (C u6 u7)) u2) = false -> (progAt (insAt (Cons (C u5 u8) u9) u2 u4) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_1049 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le u6 u2) = false -> (progAt (insAt (Cons (C u5 u8) u9) u2 u4) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_661 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_1150 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le (time (C u6 u7)) u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) (Cons (C u5 u8) u9))) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil))::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_1154 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le (time (C u6 u7)) u2) = false -> (progAt (insAt (Cons (C u5 u8) u9) u2 u4) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_740 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) (Cons (C u5 u8) u9))) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil))::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1248 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = true -> (er (C u2 u4)) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1252 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = false -> (progAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1255 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le u2 u3) = true -> (er (C u2 u4)) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1261 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le u2 u3) = true -> u4 = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1258 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le u2 u3) = false -> (progAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1371 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le u2 u3) = false -> (le (time (C u6 u7)) u3) = true -> (er (C u6 u7)) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1375 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le u2 u3) = false -> (le (time (C u6 u7)) u3) = false -> (progAt (Cons (C u5 u8) u9) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1378 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = true -> (er (C u6 u7)) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1384 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = true -> u7 = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u7)::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1381 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> (progAt (Cons (C u5 u8) u9) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1498 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> (le (time (C u5 u8)) u3) = false -> (progAt u9 u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1494 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> (le (time (C u5 u8)) u3) = true -> (er (C u5 u8)) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1501 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> (le u5 u3) = true -> (er (C u5 u8)) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1504 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> (le u5 u3) = true -> u8 = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u8)::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_743 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (progAt (insAt (Cons (C u5 u8) u9) u2 u4) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1580 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (le (time (C u5 u8)) u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u5 u8) u9)) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_1584 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (le (time (C u5 u8)) u2) = false -> (progAt (insAt u9 u2 u4) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((model_PLAN u9):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_824 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) Nil)) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_1693 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = true -> (er (C u2 u4)) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u7)::nil)).
Definition F_1697 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = false -> (progAt (Cons (C u6 u7) Nil) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_1700 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = true -> (er (C u2 u4)) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u7)::nil)).
Definition F_1706 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = true -> u4 = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(model_nat u7)::nil)).
Definition F_1703 : type_LF_276:= (fun    _ u2 u3 u6 u7 _ _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (progAt (Cons (C u6 u7) Nil) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_1809 : type_LF_276:= (fun    _ u2 u3 u6 u7 _ _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le (time (C u6 u7)) u3) = true -> (er (C u6 u7)) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(model_nat u7)::nil)).
Definition F_1813 : type_LF_276:= (fun    _ u2 u3 u6 u7 _ _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le (time (C u6 u7)) u3) = false -> (progAt Nil u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Nil nil):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_1816 : type_LF_276:= (fun    _ u2 u3 u6 u7 _ _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = true -> (er (C u6 u7)) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(model_nat u7)::nil)).
Definition F_1822 : type_LF_276:= (fun    _ u2 u3 u6 u7 _ _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = true -> u7 = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u7)::(model_nat u7)::nil)).
Definition F_1819 : type_LF_276:= (fun    _ u2 u3 u6 u7 _ _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le (time (C u6 u7)) u3) = false -> 0 = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_0 nil)::(model_nat u7)::nil)).
Definition F_1825 : type_LF_276:= (fun    _ u2 u3 u6 u7 _ _ _ => ((le u2 u3) = false -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> 0 = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_0 nil)::(model_nat u7)::nil)).
Definition F_933 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = false -> (le u6 u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) Nil)) u3) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil))::nil)):: (model_nat u3)::nil))::(Term id_0 nil)::nil)).
Definition F_1893 : type_LF_276:= (fun    _ u2 u3 u4 u6 _ _ _ => ((le u2 u3) = false -> (le u6 u3) = false -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = true -> (er (C u2 u4)) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(Term id_0 nil)::nil)).
Definition F_1897 : type_LF_276:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = false -> (le u6 u3) = false -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = false -> (progAt (Cons (C u6 u7) Nil) u3) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(Term id_0 nil)::nil)).
Definition F_1900 : type_LF_276:= (fun    _ u2 u3 u4 u6 _ _ _ => ((le u2 u3) = false -> (le u6 u3) = false -> (le u6 u2) = true -> (le u2 u3) = true -> (er (C u2 u4)) = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(Term id_0 nil)::nil)).
Definition F_1906 : type_LF_276:= (fun    _ u2 u3 u4 u6 _ _ _ => ((le u2 u3) = false -> (le u6 u3) = false -> (le u6 u2) = true -> (le u2 u3) = true -> u4 = 0, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(Term id_0 nil)::nil)).
Definition F_1046 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le u6 u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) (Cons (C u5 u8) u9))) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil))::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_2010 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = true -> (er (C u2 u4)) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u7)::nil)).
Definition F_2014 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = false -> (progAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_2017 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = true -> (er (C u2 u4)) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u7)::nil)).
Definition F_2023 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = true -> u4 = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(model_nat u7)::nil)).
Definition F_2020 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (progAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_2113 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le (time (C u6 u7)) u3) = true -> (er (C u6 u7)) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(model_nat u7)::nil)).
Definition F_2117 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le (time (C u6 u7)) u3) = false -> (progAt (Cons (C u5 u8) u9) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_2120 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = true -> (er (C u6 u7)) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(model_nat u7)::nil)).
Definition F_2126 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = true -> u7 = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u7)::(model_nat u7)::nil)).
Definition F_2123 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> (progAt (Cons (C u5 u8) u9) u3) = u7, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::(model_nat u7)::nil)).
Definition F_1157 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) (Cons (C u5 u8) u9))) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil))::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2178 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = true -> (er (C u2 u4)) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u8)::nil)).
Definition F_2182 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = false -> (progAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2185 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = true -> (er (C u2 u4)) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u8)::nil)).
Definition F_2191 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = true -> u4 = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(model_nat u8)::nil)).
Definition F_2188 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (progAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2274 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le (time (C u6 u7)) u3) = true -> (er (C u6 u7)) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(model_nat u8)::nil)).
Definition F_2278 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le (time (C u6 u7)) u3) = false -> (progAt (Cons (C u5 u8) u9) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2281 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = true -> (er (C u6 u7)) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(model_nat u8)::nil)).
Definition F_2287 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u7 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = true -> u7 = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u7)::(model_nat u8)::nil)).
Definition F_2284 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> (progAt (Cons (C u5 u8) u9) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2368 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> (le (time (C u5 u8)) u3) = true -> (er (C u5 u8)) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil))::(model_nat u8)::nil)).
Definition F_2372 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> (le (time (C u5 u8)) u3) = false -> (progAt u9 u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2375 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> (le u5 u3) = true -> (er (C u5 u8)) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil))::(model_nat u8)::nil)).
Definition F_2381 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> (le u5 u3) = true -> u8 = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u8)::(model_nat u8)::nil)).
Definition F_2378 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (le u6 u3) = false -> (le u5 u3) = false -> (progAt u9 u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_1160 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (progAt (insAt (Cons (C u5 u8) u9) u2 u4) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2425 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le (time (C u5 u8)) u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u5 u8) u9)) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2429 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le (time (C u5 u8)) u2) = false -> (progAt (insAt u9 u2 u4) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((model_PLAN u9):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2435 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le u5 u2) = false -> (progAt (insAt u9 u2 u4) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((model_PLAN u9):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_1587 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (le u5 u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u5 u8) u9)) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_2509 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (le u5 u2) = true -> (le (time (C u2 u4)) u3) = true -> (er (C u2 u4)) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_2513 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (le u5 u2) = true -> (le (time (C u2 u4)) u3) = false -> (progAt (Cons (C u5 u8) u9) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_2516 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = true -> (er (C u2 u4)) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_2522 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = true -> u4 = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_2519 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = false -> (progAt (Cons (C u5 u8) u9) u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_2600 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = false -> (le (time (C u5 u8)) u3) = false -> (progAt u9 u3) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_2596 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = false -> (le (time (C u5 u8)) u3) = true -> (er (C u5 u8)) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_2603 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = false -> (le u5 u3) = true -> (er (C u5 u8)) = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil))::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_2606 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = false -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = false -> (le u5 u3) = true -> u8 = (progAt u9 u3), (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u8)::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::nil)).
Definition F_2432 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u5 u8) u9)) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2642 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le (time (C u2 u4)) u3) = true -> (er (C u2 u4)) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u8)::nil)).
Definition F_2646 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le (time (C u2 u4)) u3) = false -> (progAt (Cons (C u5 u8) u9) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2649 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = true -> (er (C u2 u4)) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u8)::nil)).
Definition F_2655 : type_LF_276:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = true -> u4 = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(model_nat u8)::nil)).
Definition F_2652 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = false -> (progAt (Cons (C u5 u8) u9) u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2722 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = false -> (le (time (C u5 u8)) u3) = true -> (er (C u5 u8)) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil))::(model_nat u8)::nil)).
Definition F_2726 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = false -> (le (time (C u5 u8)) u3) = false -> (progAt u9 u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::(model_nat u8)::nil)).
Definition F_2729 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = false -> (le u5 u3) = true -> (er (C u5 u8)) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil))::(model_nat u8)::nil)).
Definition F_2735 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = false -> (le u5 u3) = true -> u8 = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u8)::(model_nat u8)::nil)).
Definition F_2732 : type_LF_276:= (fun   u9 u2 u3 u5 u6 u8 _ _ => ((le u2 u3) = false -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u3) = false -> (le u5 u3) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = false -> (le u5 u3) = false -> (progAt u9 u3) = u8, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((model_PLAN u9):: (model_nat u3)::nil))::(model_nat u8)::nil)).

Definition LF_276 := [F_276, F_328, F_310, F_316, F_329, F_333, F_322, F_375, F_336, F_438, F_442, F_448, F_445, F_451, F_330, F_495, F_499, F_502, F_505, F_378, F_569, F_573, F_576, F_579, F_648, F_652, F_655, F_658, F_733, F_737, F_508, F_817, F_821, F_827, F_830, F_511, F_926, F_930, F_936, F_582, F_1039, F_1043, F_1049, F_661, F_1150, F_1154, F_740, F_1248, F_1252, F_1255, F_1261, F_1258, F_1371, F_1375, F_1378, F_1384, F_1381, F_1498, F_1494, F_1501, F_1504, F_743, F_1580, F_1584, F_824, F_1693, F_1697, F_1700, F_1706, F_1703, F_1809, F_1813, F_1816, F_1822, F_1819, F_1825, F_933, F_1893, F_1897, F_1900, F_1906, F_1046, F_2010, F_2014, F_2017, F_2023, F_2020, F_2113, F_2117, F_2120, F_2126, F_2123, F_1157, F_2178, F_2182, F_2185, F_2191, F_2188, F_2274, F_2278, F_2281, F_2287, F_2284, F_2368, F_2372, F_2375, F_2381, F_2378, F_1160, F_2425, F_2429, F_2435, F_1587, F_2509, F_2513, F_2516, F_2522, F_2519, F_2600, F_2596, F_2603, F_2606, F_2432, F_2642, F_2646, F_2649, F_2655, F_2652, F_2722, F_2726, F_2729, F_2735, F_2732].


Function f_276 (u1: PLAN) {struct u1} : bool :=
 match u1 with
| Nil => true
| (Cons (C u6 u7) Nil) => true
| (Cons (C u6 u7) (Cons (C u5 u8) u9)) => true
end.

Lemma main_276 : forall F, In F LF_276 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, forall u7, forall u8, (forall F', In F' LF_276 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, forall e7, forall e8, less (snd (F' e1 e2 e3 e4 e5 e6 e7 e8)) (snd (F u1 u2 u3 u4 u5 u6 u7 u8)) -> fst (F' e1 e2 e3 e4 e5 e6 e7 e8)) -> fst (F u1 u2 u3 u4 u5 u6 u7 u8).
Proof.
intros F HF u1 u2 u3 u4 u5 u6 u7 u8; case_In HF; intro Hind.

	(* GENERATE on [ 276 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 

revert Hind.

pattern u1, (f_276 u1). apply f_276_ind.

(* case [ 310 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_310). clear HFabs0.
assert (HFabs0 : fst (F_310 Nil u2 u3 u4 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_310. unfold F_276. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_276. unfold F_310.
auto.


(* case [ 316 ] *)

intros _u1. intro u6. intro u7.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_316). clear HFabs0.
assert (HFabs0 : fst (F_316 Nil u2 u3 u4 u6 u7 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_316. unfold F_276. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_276. unfold F_316.
auto.



intros _u1. intro u6. intro u7. intro u5. intro u8. intro u9.  intro eq_1.  intro HFabs0.
case_eq (le u5 u6); [intro H | intro H].

(* case [ 322 ] *)

assert (Hind := HFabs0 F_322). clear HFabs0.
assert (HFabs0 : fst (F_322 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Hind. trivial_in 6. unfold snd. unfold F_322. unfold F_276. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_276. unfold F_322. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 328 ] *)

assert (Hind := HFabs0 F_328). clear HFabs0.
assert (HFabs0 : fst (F_328 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Hind. trivial_in 1. unfold snd. unfold F_328. unfold F_276. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_276. unfold F_328. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 328 ] *)

unfold fst. unfold F_328. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 310 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (H := Hind F_329). 
assert (HFabs0 : fst (F_329 Nil u2 u3 u4 0 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_329. unfold F_310. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_310. unfold F_329.

unfold fst in HFabs0. unfold F_329 in HFabs0.
auto.



	(* NEGATIVE DECOMPOSITION on [ 316 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (H := Hind F_330). 
assert (HFabs0 : fst (F_330 Nil u2 u3 u4 u6 u7 0 0)).
apply H. trivial_in 14. unfold snd. unfold F_330. unfold F_316. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_316. unfold F_330.

unfold fst in HFabs0. unfold F_330 in HFabs0.
auto.



	(* REWRITING on [ 329 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_333). clear Hind.
assert (HFabs1 : fst (F_333 Nil u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_333. unfold F_329. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_329. unfold fst in HFabs1. unfold F_333 in HFabs1.   
pattern u3. simpl (progAt _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 333 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_336). clear Hind.
assert (HFabs1 : fst (F_336 Nil u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 8. unfold snd. unfold F_336. unfold F_333. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_333. unfold fst in HFabs1. unfold F_336 in HFabs1.   
pattern u2, u4. simpl (insAt _ _ _). cbv beta.
 simpl. auto.



	(* AUGMENTATION on [ 322 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H := Hind F_375). clear Hind.
assert (HFabs0: fst (F_375 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H. trivial_in 7. unfold snd. unfold F_322. unfold F_375. rewrite_model. abstract solve_rpo_mul.

unfold fst. unfold F_322.

specialize true_231 with (u1 := (C u5 u8)) (u2 := u9).
specialize true_199 with (u1 := (C u5 u8)) (u2 := u9). auto.




	(* REWRITING on [ 375 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_378). clear Hind.
assert (HFabs1 : fst (F_378 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 19. unfold snd. unfold F_378. unfold F_375. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_375. unfold fst in HFabs1. unfold F_378 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 336 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (H: ((le (time (C u2 u4)) u3) = true) \/ ((le (time (C u2 u4)) u3) = false)). 

destruct ((le (time (C u2 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_438). clear Hind.
assert (HFabs0 : fst (F_438 Nil u2 u3 u4 0 0 0 0)).
apply H1. trivial_in 9. unfold snd. unfold F_438. unfold F_336. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_336. unfold F_438. unfold fst in HFabs0. unfold F_438 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern Nil.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_442). clear Hind.
assert (HFabs0 : fst (F_442 Nil u2 u3 u4 0 0 0 0)).
apply H1. trivial_in 10. unfold snd. unfold F_442. unfold F_336. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_336. unfold F_442. unfold fst in HFabs0. unfold F_442 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern Nil.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 438 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_445). clear Hind.
assert (HFabs1 : fst (F_445 Nil u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 12. unfold snd. unfold F_445. unfold F_438. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_438. unfold fst in HFabs1. unfold F_445 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 442 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_448). clear Hind.
assert (HFabs1 : fst (F_448 Nil u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 11. unfold snd. unfold F_448. unfold F_442. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_442. unfold fst in HFabs1. unfold F_448 in HFabs1.   
pattern u3. simpl (progAt _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 448 ] *)

unfold fst. unfold F_448.
auto.



	(* REWRITING on [ 445 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_451). clear Hind.
assert (HFabs1 : fst (F_451 Nil u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 13. unfold snd. unfold F_451. unfold F_445. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_445. unfold fst in HFabs1. unfold F_451 in HFabs1.   
pattern u2, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 451 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
unfold fst. unfold F_451. specialize true_159 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 330 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u6 u7)) u3) = true) \/ ((le (time (C u6 u7)) u3) = false)). 

destruct ((le (time (C u6 u7)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_495). clear Hind.
assert (HFabs0 : fst (F_495 Nil u2 u3 u4 u6 u7 0 0)).
apply H1. trivial_in 15. unfold snd. unfold F_495. unfold F_330. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_330. unfold F_495. unfold fst in HFabs0. unfold F_495 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u3.
pattern Nil.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_499). clear Hind.
assert (HFabs0 : fst (F_499 Nil u2 u3 u4 u6 u7 0 0)).
apply H1. trivial_in 16. unfold snd. unfold F_499. unfold F_330. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_330. unfold F_499. unfold fst in HFabs0. unfold F_499 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u3.
pattern Nil.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 495 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_502). clear Hind.
assert (HFabs1 : fst (F_502 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 17. unfold snd. unfold F_502. unfold F_495. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_495. unfold fst in HFabs1. unfold F_502 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 499 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_505). clear Hind.
assert (HFabs1 : fst (F_505 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 18. unfold snd. unfold F_505. unfold F_499. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_499. unfold fst in HFabs1. unfold F_505 in HFabs1.   
pattern u3. simpl (progAt _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 502 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_508). clear Hind.
assert (HFabs1 : fst (F_508 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 30. unfold snd. unfold F_508. unfold F_502. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_502. unfold fst in HFabs1. unfold F_508 in HFabs1.   
pattern u6, u7. simpl (er _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 505 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_511). clear Hind.
assert (HFabs1 : fst (F_511 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 35. unfold snd. unfold F_511. unfold F_505. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_505. unfold fst in HFabs1. unfold F_511 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 378 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u6 u7)) u3) = true) \/ ((le (time (C u6 u7)) u3) = false)). 

destruct ((le (time (C u6 u7)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_569). clear Hind.
assert (HFabs0 : fst (F_569 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 20. unfold snd. unfold F_569. unfold F_378. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_378. unfold F_569. unfold fst in HFabs0. unfold F_569 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_573). clear Hind.
assert (HFabs0 : fst (F_573 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 21. unfold snd. unfold F_573. unfold F_378. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_378. unfold F_573. unfold fst in HFabs0. unfold F_573 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 569 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_576). clear Hind.
assert (HFabs1 : fst (F_576 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 22. unfold snd. unfold F_576. unfold F_569. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_569. unfold fst in HFabs1. unfold F_576 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 573 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_579). clear Hind.
assert (HFabs1 : fst (F_579 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 23. unfold snd. unfold F_579. unfold F_573. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_573. unfold fst in HFabs1. unfold F_579 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 576 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_582). clear Hind.
assert (HFabs1 : fst (F_582 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 39. unfold snd. unfold F_582. unfold F_576. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_576. unfold fst in HFabs1. unfold F_582 in HFabs1.   
pattern u6, u7. simpl (er _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 579 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u5 u8)) u3) = true) \/ ((le (time (C u5 u8)) u3) = false)). 

destruct ((le (time (C u5 u8)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_648). clear Hind.
assert (HFabs0 : fst (F_648 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 24. unfold snd. unfold F_648. unfold F_579. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_579. unfold F_648. unfold fst in HFabs0. unfold F_648 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u3.
pattern u9.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_652). clear Hind.
assert (HFabs0 : fst (F_652 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 25. unfold snd. unfold F_652. unfold F_579. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_579. unfold F_652. unfold fst in HFabs0. unfold F_652 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u3.
pattern u9.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 648 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_655). clear Hind.
assert (HFabs1 : fst (F_655 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 26. unfold snd. unfold F_655. unfold F_648. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_648. unfold fst in HFabs1. unfold F_655 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 652 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_658). clear Hind.
assert (HFabs1 : fst (F_658 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 27. unfold snd. unfold F_658. unfold F_652. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_652. unfold fst in HFabs1. unfold F_658 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 655 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_661). clear Hind.
assert (HFabs1 : fst (F_661 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 43. unfold snd. unfold F_661. unfold F_655. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_655. unfold fst in HFabs1. unfold F_661 in HFabs1.   
pattern u5, u8. simpl (er _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 658 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u6 u7)) u2) = true) \/ ((le (time (C u6 u7)) u2) = false)). 

destruct ((le (time (C u6 u7)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 131 ] *)

assert (H1 := Hind F_733). clear Hind.
assert (HFabs0 : fst (F_733 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 28. unfold snd. unfold F_733. unfold F_658. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_658. unfold F_733. unfold fst in HFabs0. unfold F_733 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern (Cons (C u5 u8) u9).
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 132 ] *)

assert (H1 := Hind F_737). clear Hind.
assert (HFabs0 : fst (F_737 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 29. unfold snd. unfold F_737. unfold F_658. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_658. unfold F_737. unfold fst in HFabs0. unfold F_737 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern (Cons (C u5 u8) u9).
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 733 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_740). clear Hind.
assert (HFabs1 : fst (F_740 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 46. unfold snd. unfold F_740. unfold F_733. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_733. unfold fst in HFabs1. unfold F_740 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 737 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_743). clear Hind.
assert (HFabs1 : fst (F_743 u9 u2 u3 u4 u5 u6 u8 0)).
apply Res. trivial_in 61. unfold snd. unfold F_743. unfold F_737. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_737. unfold fst in HFabs1. unfold F_743 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 508 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u6 u7)) u2) = true) \/ ((le (time (C u6 u7)) u2) = false)). 

destruct ((le (time (C u6 u7)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 131 ] *)

assert (H1 := Hind F_817). clear Hind.
assert (HFabs0 : fst (F_817 Nil u2 u3 u4 u6 u7 0 0)).
apply H1. trivial_in 31. unfold snd. unfold F_817. unfold F_508. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_508. unfold F_817. unfold fst in HFabs0. unfold F_817 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern Nil.
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 132 ] *)

assert (H1 := Hind F_821). clear Hind.
assert (HFabs0 : fst (F_821 Nil u2 u3 u4 u6 u7 0 0)).
apply H1. trivial_in 32. unfold snd. unfold F_821. unfold F_508. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_508. unfold F_821. unfold fst in HFabs0. unfold F_821 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern Nil.
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 817 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_824). clear Hind.
assert (HFabs1 : fst (F_824 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 64. unfold snd. unfold F_824. unfold F_817. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_817. unfold fst in HFabs1. unfold F_824 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 821 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_827). clear Hind.
assert (HFabs1 : fst (F_827 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 33. unfold snd. unfold F_827. unfold F_821. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_821. unfold fst in HFabs1. unfold F_827 in HFabs1.   
pattern u2, u4. simpl (insAt _ _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 827 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_830). clear Hind.
assert (HFabs1 : fst (F_830 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 34. unfold snd. unfold F_830. unfold F_827. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_827. unfold fst in HFabs1. unfold F_830 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 830 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
unfold fst. unfold F_830. specialize true_154 with (u1 := u6) (u2 := u3) (u3 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 511 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u6 u7)) u2) = true) \/ ((le (time (C u6 u7)) u2) = false)). 

destruct ((le (time (C u6 u7)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 131 ] *)

assert (H1 := Hind F_926). clear Hind.
assert (HFabs0 : fst (F_926 Nil u2 u3 u4 u6 u7 0 0)).
apply H1. trivial_in 36. unfold snd. unfold F_926. unfold F_511. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_511. unfold F_926. unfold fst in HFabs0. unfold F_926 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern Nil.
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 132 ] *)

assert (H1 := Hind F_930). clear Hind.
assert (HFabs0 : fst (F_930 Nil u2 u3 u4 u6 u7 0 0)).
apply H1. trivial_in 37. unfold snd. unfold F_930. unfold F_511. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_511. unfold F_930. unfold fst in HFabs0. unfold F_930 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern Nil.
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 926 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_933). clear Hind.
assert (HFabs1 : fst (F_933 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 76. unfold snd. unfold F_933. unfold F_926. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_926. unfold fst in HFabs1. unfold F_933 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 930 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_936). clear Hind.
assert (HFabs1 : fst (F_936 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 38. unfold snd. unfold F_936. unfold F_930. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_930. unfold fst in HFabs1. unfold F_936 in HFabs1.   
pattern u2, u4. simpl (insAt _ _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 936 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_336). clear Hind.
assert (HFabs1 : fst (F_336 Nil u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 8. unfold snd. unfold F_336. unfold F_936. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_936. unfold fst in HFabs1. unfold F_336 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 582 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u6 u7)) u2) = true) \/ ((le (time (C u6 u7)) u2) = false)). 

destruct ((le (time (C u6 u7)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 131 ] *)

assert (H1 := Hind F_1039). clear Hind.
assert (HFabs0 : fst (F_1039 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 40. unfold snd. unfold F_1039. unfold F_582. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_582. unfold F_1039. unfold fst in HFabs0. unfold F_1039 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern (Cons (C u5 u8) u9).
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 132 ] *)

assert (H1 := Hind F_1043). clear Hind.
assert (HFabs0 : fst (F_1043 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 41. unfold snd. unfold F_1043. unfold F_582. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_582. unfold F_1043. unfold fst in HFabs0. unfold F_1043 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern (Cons (C u5 u8) u9).
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 1039 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_1046). clear Hind.
assert (HFabs1 : fst (F_1046 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 81. unfold snd. unfold F_1046. unfold F_1039. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1039. unfold fst in HFabs1. unfold F_1046 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1043 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_1049). clear Hind.
assert (HFabs1 : fst (F_1049 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 42. unfold snd. unfold F_1049. unfold F_1043. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1043. unfold fst in HFabs1. unfold F_1049 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 1049 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
unfold fst. unfold F_1049. specialize true_154 with (u1 := u6) (u2 := u3) (u3 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 661 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u6 u7)) u2) = true) \/ ((le (time (C u6 u7)) u2) = false)). 

destruct ((le (time (C u6 u7)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 131 ] *)

assert (H1 := Hind F_1150). clear Hind.
assert (HFabs0 : fst (F_1150 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 44. unfold snd. unfold F_1150. unfold F_661. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_661. unfold F_1150. unfold fst in HFabs0. unfold F_1150 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern (Cons (C u5 u8) u9).
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 132 ] *)

assert (H1 := Hind F_1154). clear Hind.
assert (HFabs0 : fst (F_1154 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 45. unfold snd. unfold F_1154. unfold F_661. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_661. unfold F_1154. unfold fst in HFabs0. unfold F_1154 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern (Cons (C u5 u8) u9).
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 1150 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_1157). clear Hind.
assert (HFabs1 : fst (F_1157 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 92. unfold snd. unfold F_1157. unfold F_1150. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1150. unfold fst in HFabs1. unfold F_1157 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1154 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_1160). clear Hind.
assert (HFabs1 : fst (F_1160 u9 u2 u3 u4 u5 u6 u8 0)).
apply Res. trivial_in 108. unfold snd. unfold F_1160. unfold F_1154. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1154. unfold fst in HFabs1. unfold F_1160 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 740 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u2 u4)) u3) = true) \/ ((le (time (C u2 u4)) u3) = false)). 

destruct ((le (time (C u2 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_1248). clear Hind.
assert (HFabs0 : fst (F_1248 u9 u2 u3 u4 u5 u6 0 0)).
apply H1. trivial_in 47. unfold snd. unfold F_1248. unfold F_740. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_740. unfold F_1248. unfold fst in HFabs0. unfold F_1248 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) (Cons (C u5 u8) u9)).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_1252). clear Hind.
assert (HFabs0 : fst (F_1252 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 48. unfold snd. unfold F_1252. unfold F_740. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_740. unfold F_1252. unfold fst in HFabs0. unfold F_1252 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) (Cons (C u5 u8) u9)).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 1248 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_1255). clear Hind.
assert (HFabs1 : fst (F_1255 u9 u2 u3 u4 u5 u6 0 0)).
apply Res. trivial_in 49. unfold snd. unfold F_1255. unfold F_1248. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1248. unfold fst in HFabs1. unfold F_1255 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1252 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_1258). clear Hind.
assert (HFabs1 : fst (F_1258 u9 u2 u3 u5 u6 u7 u8 0)).
apply Res. trivial_in 51. unfold snd. unfold F_1258. unfold F_1252. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1252. unfold fst in HFabs1. unfold F_1258 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1255 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_1261). clear Hind.
assert (HFabs1 : fst (F_1261 u9 u2 u3 u4 u5 u6 0 0)).
apply Res. trivial_in 50. unfold snd. unfold F_1261. unfold F_1255. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1255. unfold fst in HFabs1. unfold F_1261 in HFabs1.   
pattern u2, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 1261 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
unfold fst. unfold F_1261. specialize true_159 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 1258 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u6 u7)) u3) = true) \/ ((le (time (C u6 u7)) u3) = false)). 

destruct ((le (time (C u6 u7)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_1371). clear Hind.
assert (HFabs0 : fst (F_1371 u9 u2 u3 u5 u6 u7 0 0)).
apply H1. trivial_in 52. unfold snd. unfold F_1371. unfold F_1258. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1258. unfold F_1371. unfold fst in HFabs0. unfold F_1371 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_1375). clear Hind.
assert (HFabs0 : fst (F_1375 u9 u2 u3 u5 u6 u7 u8 0)).
apply H1. trivial_in 53. unfold snd. unfold F_1375. unfold F_1258. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1258. unfold F_1375. unfold fst in HFabs0. unfold F_1375 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 1371 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_1378). clear Hind.
assert (HFabs1 : fst (F_1378 u9 u2 u3 u5 u6 u7 0 0)).
apply Res. trivial_in 54. unfold snd. unfold F_1378. unfold F_1371. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1371. unfold fst in HFabs1. unfold F_1378 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1375 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_1381). clear Hind.
assert (HFabs1 : fst (F_1381 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 56. unfold snd. unfold F_1381. unfold F_1375. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1375. unfold fst in HFabs1. unfold F_1381 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1378 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_1384). clear Hind.
assert (HFabs1 : fst (F_1384 u9 u2 u3 u5 u6 u7 0 0)).
apply Res. trivial_in 55. unfold snd. unfold F_1384. unfold F_1378. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1378. unfold fst in HFabs1. unfold F_1384 in HFabs1.   
pattern u6, u7. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 1384 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
unfold fst. unfold F_1384. specialize true_159 with (u1 := u6) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 1381 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (H: ((le (time (C u5 u8)) u3) = true) \/ ((le (time (C u5 u8)) u3) = false)). 

destruct ((le (time (C u5 u8)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_1494). clear Hind.
assert (HFabs0 : fst (F_1494 u9 u2 u3 u5 u6 u8 0 0)).
apply H1. trivial_in 58. unfold snd. unfold F_1494. unfold F_1381. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1381. unfold F_1494. unfold fst in HFabs0. unfold F_1494 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u3.
pattern u9.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_1498). clear Hind.
assert (HFabs0 : fst (F_1498 u9 u2 u3 u5 u6 u8 0 0)).
apply H1. trivial_in 57. unfold snd. unfold F_1498. unfold F_1381. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1381. unfold F_1498. unfold fst in HFabs0. unfold F_1498 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u3.
pattern u9.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 1498 ] *)

unfold fst. unfold F_1498.
auto.



	(* REWRITING on [ 1494 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_1501). clear Hind.
assert (HFabs1 : fst (F_1501 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 59. unfold snd. unfold F_1501. unfold F_1494. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1494. unfold fst in HFabs1. unfold F_1501 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1501 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_1504). clear Hind.
assert (HFabs1 : fst (F_1504 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 60. unfold snd. unfold F_1504. unfold F_1501. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1501. unfold fst in HFabs1. unfold F_1504 in HFabs1.   
pattern u5, u8. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 1504 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
unfold fst. unfold F_1504. specialize true_159 with (u1 := u5) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 743 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (H: ((le (time (C u5 u8)) u2) = true) \/ ((le (time (C u5 u8)) u2) = false)). 

destruct ((le (time (C u5 u8)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 131 ] *)

assert (H1 := Hind F_1580). clear Hind.
assert (HFabs0 : fst (F_1580 u9 u2 u3 u4 u5 u6 u8 0)).
apply H1. trivial_in 62. unfold snd. unfold F_1580. unfold F_743. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_743. unfold F_1580. unfold fst in HFabs0. unfold F_1580 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u2.
pattern u9.
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 132 ] *)

assert (H1 := Hind F_1584). clear Hind.
assert (HFabs0 : fst (F_1584 u9 u2 u3 u4 u5 u6 u8 0)).
apply H1. trivial_in 63. unfold snd. unfold F_1584. unfold F_743. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_743. unfold F_1584. unfold fst in HFabs0. unfold F_1584 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u2.
pattern u9.
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 1580 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_1587). clear Hind.
assert (HFabs1 : fst (F_1587 u9 u2 u3 u4 u5 u6 u8 0)).
apply Res. trivial_in 112. unfold snd. unfold F_1587. unfold F_1580. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1580. unfold fst in HFabs1. unfold F_1587 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1584 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_276). clear Hind.
assert (HFabs1 : fst (F_276 u9 u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 0. unfold snd. unfold F_276. unfold F_1584. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1584. unfold fst in HFabs1. unfold F_276 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 824 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u2 u4)) u3) = true) \/ ((le (time (C u2 u4)) u3) = false)). 

destruct ((le (time (C u2 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_1693). clear Hind.
assert (HFabs0 : fst (F_1693 Nil u2 u3 u4 u6 u7 0 0)).
apply H1. trivial_in 65. unfold snd. unfold F_1693. unfold F_824. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_824. unfold F_1693. unfold fst in HFabs0. unfold F_1693 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) Nil).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_1697). clear Hind.
assert (HFabs0 : fst (F_1697 Nil u2 u3 u4 u6 u7 0 0)).
apply H1. trivial_in 66. unfold snd. unfold F_1697. unfold F_824. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_824. unfold F_1697. unfold fst in HFabs0. unfold F_1697 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) Nil).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 1693 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_1700). clear Hind.
assert (HFabs1 : fst (F_1700 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 67. unfold snd. unfold F_1700. unfold F_1693. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1693. unfold fst in HFabs1. unfold F_1700 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1697 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_1703). clear Hind.
assert (HFabs1 : fst (F_1703 Nil u2 u3 u6 u7 0 0 0)).
apply Res. trivial_in 69. unfold snd. unfold F_1703. unfold F_1697. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1697. unfold fst in HFabs1. unfold F_1703 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1700 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_1706). clear Hind.
assert (HFabs1 : fst (F_1706 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 68. unfold snd. unfold F_1706. unfold F_1700. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1700. unfold fst in HFabs1. unfold F_1706 in HFabs1.   
pattern u2, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 1706 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
unfold fst. unfold F_1706. specialize true_159 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 1703 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u6. rename u5 into _u7. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u6 u7)) u3) = true) \/ ((le (time (C u6 u7)) u3) = false)). 

destruct ((le (time (C u6 u7)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_1809). clear Hind.
assert (HFabs0 : fst (F_1809 Nil u2 u3 u6 u7 0 0 0)).
apply H1. trivial_in 70. unfold snd. unfold F_1809. unfold F_1703. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1703. unfold F_1809. unfold fst in HFabs0. unfold F_1809 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u3.
pattern Nil.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_1813). clear Hind.
assert (HFabs0 : fst (F_1813 Nil u2 u3 u6 u7 0 0 0)).
apply H1. trivial_in 71. unfold snd. unfold F_1813. unfold F_1703. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1703. unfold F_1813. unfold fst in HFabs0. unfold F_1813 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u3.
pattern Nil.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 1809 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u6. rename u5 into _u7. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_1816). clear Hind.
assert (HFabs1 : fst (F_1816 Nil u2 u3 u6 u7 0 0 0)).
apply Res. trivial_in 72. unfold snd. unfold F_1816. unfold F_1809. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1809. unfold fst in HFabs1. unfold F_1816 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1813 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u6. rename u5 into _u7. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_1819). clear Hind.
assert (HFabs1 : fst (F_1819 Nil u2 u3 u6 u7 0 0 0)).
apply Res. trivial_in 74. unfold snd. unfold F_1819. unfold F_1813. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1813. unfold fst in HFabs1. unfold F_1819 in HFabs1.   
pattern u3. simpl (progAt _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1816 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u6. rename u5 into _u7. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_1822). clear Hind.
assert (HFabs1 : fst (F_1822 Nil u2 u3 u6 u7 0 0 0)).
apply Res. trivial_in 73. unfold snd. unfold F_1822. unfold F_1816. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1816. unfold fst in HFabs1. unfold F_1822 in HFabs1.   
pattern u6, u7. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 1822 ] *)

unfold fst. unfold F_1822.
auto.



	(* REWRITING on [ 1819 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u6. rename u5 into _u7. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_1825). clear Hind.
assert (HFabs1 : fst (F_1825 Nil u2 u3 u6 u7 0 0 0)).
apply Res. trivial_in 75. unfold snd. unfold F_1825. unfold F_1819. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1819. unfold fst in HFabs1. unfold F_1825 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 1825 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u6. rename u5 into _u7. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u6 into u6. rename _u7 into u7. 
unfold fst. unfold F_1825. specialize true_159 with (u1 := u6) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 933 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u2 u4)) u3) = true) \/ ((le (time (C u2 u4)) u3) = false)). 

destruct ((le (time (C u2 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_1893). clear Hind.
assert (HFabs0 : fst (F_1893 Nil u2 u3 u4 u6 0 0 0)).
apply H1. trivial_in 77. unfold snd. unfold F_1893. unfold F_933. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_933. unfold F_1893. unfold fst in HFabs0. unfold F_1893 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) Nil).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_1897). clear Hind.
assert (HFabs0 : fst (F_1897 Nil u2 u3 u4 u6 u7 0 0)).
apply H1. trivial_in 78. unfold snd. unfold F_1897. unfold F_933. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_933. unfold F_1897. unfold fst in HFabs0. unfold F_1897 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) Nil).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 1893 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_1900). clear Hind.
assert (HFabs1 : fst (F_1900 Nil u2 u3 u4 u6 0 0 0)).
apply Res. trivial_in 79. unfold snd. unfold F_1900. unfold F_1893. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1893. unfold fst in HFabs1. unfold F_1900 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1897 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_336). clear Hind.
assert (HFabs1 : fst (F_336 Nil u6 u3 u7 0 0 0 0)).
apply Res. trivial_in 8. unfold snd. unfold F_336. unfold F_1897. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1897. unfold fst in HFabs1. unfold F_336 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 1900 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_1906). clear Hind.
assert (HFabs1 : fst (F_1906 Nil u2 u3 u4 u6 0 0 0)).
apply Res. trivial_in 80. unfold snd. unfold F_1906. unfold F_1900. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1900. unfold fst in HFabs1. unfold F_1906 in HFabs1.   
pattern u2, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 1906 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
unfold fst. unfold F_1906. specialize true_159 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 1046 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u2 u4)) u3) = true) \/ ((le (time (C u2 u4)) u3) = false)). 

destruct ((le (time (C u2 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_2010). clear Hind.
assert (HFabs0 : fst (F_2010 u9 u2 u3 u4 u5 u6 u7 0)).
apply H1. trivial_in 82. unfold snd. unfold F_2010. unfold F_1046. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1046. unfold F_2010. unfold fst in HFabs0. unfold F_2010 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) (Cons (C u5 u8) u9)).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_2014). clear Hind.
assert (HFabs0 : fst (F_2014 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 83. unfold snd. unfold F_2014. unfold F_1046. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1046. unfold F_2014. unfold fst in HFabs0. unfold F_2014 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) (Cons (C u5 u8) u9)).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 2010 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_2017). clear Hind.
assert (HFabs1 : fst (F_2017 u9 u2 u3 u4 u5 u6 u7 0)).
apply Res. trivial_in 84. unfold snd. unfold F_2017. unfold F_2010. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2010. unfold fst in HFabs1. unfold F_2017 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2014 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_2020). clear Hind.
assert (HFabs1 : fst (F_2020 u9 u2 u3 u5 u6 u7 u8 0)).
apply Res. trivial_in 86. unfold snd. unfold F_2020. unfold F_2014. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2014. unfold fst in HFabs1. unfold F_2020 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2017 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_2023). clear Hind.
assert (HFabs1 : fst (F_2023 u9 u2 u3 u4 u5 u6 u7 0)).
apply Res. trivial_in 85. unfold snd. unfold F_2023. unfold F_2017. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2017. unfold fst in HFabs1. unfold F_2023 in HFabs1.   
pattern u2, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 2023 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
unfold fst. unfold F_2023. specialize true_159 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 2020 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u6 u7)) u3) = true) \/ ((le (time (C u6 u7)) u3) = false)). 

destruct ((le (time (C u6 u7)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_2113). clear Hind.
assert (HFabs0 : fst (F_2113 u9 u2 u3 u5 u6 u7 0 0)).
apply H1. trivial_in 87. unfold snd. unfold F_2113. unfold F_2020. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2020. unfold F_2113. unfold fst in HFabs0. unfold F_2113 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_2117). clear Hind.
assert (HFabs0 : fst (F_2117 u9 u2 u3 u5 u6 u7 u8 0)).
apply H1. trivial_in 88. unfold snd. unfold F_2117. unfold F_2020. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2020. unfold F_2117. unfold fst in HFabs0. unfold F_2117 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 2113 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_2120). clear Hind.
assert (HFabs1 : fst (F_2120 u9 u2 u3 u5 u6 u7 0 0)).
apply Res. trivial_in 89. unfold snd. unfold F_2120. unfold F_2113. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2113. unfold fst in HFabs1. unfold F_2120 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2117 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_2123). clear Hind.
assert (HFabs1 : fst (F_2123 u9 u2 u3 u5 u6 u7 u8 0)).
apply Res. trivial_in 91. unfold snd. unfold F_2123. unfold F_2117. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2117. unfold fst in HFabs1. unfold F_2123 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2120 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_2126). clear Hind.
assert (HFabs1 : fst (F_2126 u9 u2 u3 u5 u6 u7 0 0)).
apply Res. trivial_in 90. unfold snd. unfold F_2126. unfold F_2120. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2120. unfold fst in HFabs1. unfold F_2126 in HFabs1.   
pattern u6, u7. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 2126 ] *)

unfold fst. unfold F_2126.
auto.



	(* SUBSUMPTION on [ 2123 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
unfold fst. unfold F_2123. specialize true_159 with (u1 := u6) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 1157 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u2 u4)) u3) = true) \/ ((le (time (C u2 u4)) u3) = false)). 

destruct ((le (time (C u2 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_2178). clear Hind.
assert (HFabs0 : fst (F_2178 u9 u2 u3 u4 u5 u6 u8 0)).
apply H1. trivial_in 93. unfold snd. unfold F_2178. unfold F_1157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1157. unfold F_2178. unfold fst in HFabs0. unfold F_2178 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) (Cons (C u5 u8) u9)).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_2182). clear Hind.
assert (HFabs0 : fst (F_2182 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 94. unfold snd. unfold F_2182. unfold F_1157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1157. unfold F_2182. unfold fst in HFabs0. unfold F_2182 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) (Cons (C u5 u8) u9)).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 2178 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2185). clear Hind.
assert (HFabs1 : fst (F_2185 u9 u2 u3 u4 u5 u6 u8 0)).
apply Res. trivial_in 95. unfold snd. unfold F_2185. unfold F_2178. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2178. unfold fst in HFabs1. unfold F_2185 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2182 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_2188). clear Hind.
assert (HFabs1 : fst (F_2188 u9 u2 u3 u5 u6 u7 u8 0)).
apply Res. trivial_in 97. unfold snd. unfold F_2188. unfold F_2182. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2182. unfold fst in HFabs1. unfold F_2188 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2185 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2191). clear Hind.
assert (HFabs1 : fst (F_2191 u9 u2 u3 u4 u5 u6 u8 0)).
apply Res. trivial_in 96. unfold snd. unfold F_2191. unfold F_2185. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2185. unfold fst in HFabs1. unfold F_2191 in HFabs1.   
pattern u2, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 2191 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
unfold fst. unfold F_2191. specialize true_159 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 2188 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u6 u7)) u3) = true) \/ ((le (time (C u6 u7)) u3) = false)). 

destruct ((le (time (C u6 u7)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_2274). clear Hind.
assert (HFabs0 : fst (F_2274 u9 u2 u3 u5 u6 u7 u8 0)).
apply H1. trivial_in 98. unfold snd. unfold F_2274. unfold F_2188. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2188. unfold F_2274. unfold fst in HFabs0. unfold F_2274 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_2278). clear Hind.
assert (HFabs0 : fst (F_2278 u9 u2 u3 u5 u6 u7 u8 0)).
apply H1. trivial_in 99. unfold snd. unfold F_2278. unfold F_2188. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2188. unfold F_2278. unfold fst in HFabs0. unfold F_2278 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 2274 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_2281). clear Hind.
assert (HFabs1 : fst (F_2281 u9 u2 u3 u5 u6 u7 u8 0)).
apply Res. trivial_in 100. unfold snd. unfold F_2281. unfold F_2274. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2274. unfold fst in HFabs1. unfold F_2281 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2278 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_2284). clear Hind.
assert (HFabs1 : fst (F_2284 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 102. unfold snd. unfold F_2284. unfold F_2278. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2278. unfold fst in HFabs1. unfold F_2284 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2281 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_2287). clear Hind.
assert (HFabs1 : fst (F_2287 u9 u2 u3 u5 u6 u7 u8 0)).
apply Res. trivial_in 101. unfold snd. unfold F_2287. unfold F_2281. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2281. unfold fst in HFabs1. unfold F_2287 in HFabs1.   
pattern u6, u7. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 2287 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u7. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
unfold fst. unfold F_2287. specialize true_159 with (u1 := u6) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 2284 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (H: ((le (time (C u5 u8)) u3) = true) \/ ((le (time (C u5 u8)) u3) = false)). 

destruct ((le (time (C u5 u8)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_2368). clear Hind.
assert (HFabs0 : fst (F_2368 u9 u2 u3 u5 u6 u8 0 0)).
apply H1. trivial_in 103. unfold snd. unfold F_2368. unfold F_2284. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2284. unfold F_2368. unfold fst in HFabs0. unfold F_2368 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u3.
pattern u9.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_2372). clear Hind.
assert (HFabs0 : fst (F_2372 u9 u2 u3 u5 u6 u8 0 0)).
apply H1. trivial_in 104. unfold snd. unfold F_2372. unfold F_2284. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2284. unfold F_2372. unfold fst in HFabs0. unfold F_2372 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u3.
pattern u9.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 2368 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2375). clear Hind.
assert (HFabs1 : fst (F_2375 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 105. unfold snd. unfold F_2375. unfold F_2368. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2368. unfold fst in HFabs1. unfold F_2375 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2372 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2378). clear Hind.
assert (HFabs1 : fst (F_2378 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 107. unfold snd. unfold F_2378. unfold F_2372. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2372. unfold fst in HFabs1. unfold F_2378 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2375 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2381). clear Hind.
assert (HFabs1 : fst (F_2381 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 106. unfold snd. unfold F_2381. unfold F_2375. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2375. unfold fst in HFabs1. unfold F_2381 in HFabs1.   
pattern u5, u8. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 2381 ] *)

unfold fst. unfold F_2381.
auto.



	(* SUBSUMPTION on [ 2378 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
unfold fst. unfold F_2378. specialize true_159 with (u1 := u5) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 1160 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (H: ((le (time (C u5 u8)) u2) = true) \/ ((le (time (C u5 u8)) u2) = false)). 

destruct ((le (time (C u5 u8)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 131 ] *)

assert (H1 := Hind F_2425). clear Hind.
assert (HFabs0 : fst (F_2425 u9 u2 u3 u4 u5 u6 u8 0)).
apply H1. trivial_in 109. unfold snd. unfold F_2425. unfold F_1160. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1160. unfold F_2425. unfold fst in HFabs0. unfold F_2425 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u2.
pattern u9.
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 132 ] *)

assert (H1 := Hind F_2429). clear Hind.
assert (HFabs0 : fst (F_2429 u9 u2 u3 u4 u5 u6 u8 0)).
apply H1. trivial_in 110. unfold snd. unfold F_2429. unfold F_1160. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1160. unfold F_2429. unfold fst in HFabs0. unfold F_2429 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u2.
pattern u9.
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 2425 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2432). clear Hind.
assert (HFabs1 : fst (F_2432 u9 u2 u3 u4 u5 u6 u8 0)).
apply Res. trivial_in 122. unfold snd. unfold F_2432. unfold F_2425. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2425. unfold fst in HFabs1. unfold F_2432 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2429 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2435). clear Hind.
assert (HFabs1 : fst (F_2435 u9 u2 u3 u4 u5 u6 u8 0)).
apply Res. trivial_in 111. unfold snd. unfold F_2435. unfold F_2429. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2429. unfold fst in HFabs1. unfold F_2435 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 2435 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
unfold fst. unfold F_2435. specialize true_154 with (u1 := u5) (u2 := u3) (u3 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 1587 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (H: ((le (time (C u2 u4)) u3) = true) \/ ((le (time (C u2 u4)) u3) = false)). 

destruct ((le (time (C u2 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_2509). clear Hind.
assert (HFabs0 : fst (F_2509 u9 u2 u3 u4 u5 u6 0 0)).
apply H1. trivial_in 113. unfold snd. unfold F_2509. unfold F_1587. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1587. unfold F_2509. unfold fst in HFabs0. unfold F_2509 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_2513). clear Hind.
assert (HFabs0 : fst (F_2513 u9 u2 u3 u4 u5 u6 u8 0)).
apply H1. trivial_in 114. unfold snd. unfold F_2513. unfold F_1587. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_1587. unfold F_2513. unfold fst in HFabs0. unfold F_2513 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 2509 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_2516). clear Hind.
assert (HFabs1 : fst (F_2516 u9 u2 u3 u4 u5 u6 0 0)).
apply Res. trivial_in 115. unfold snd. unfold F_2516. unfold F_2509. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2509. unfold fst in HFabs1. unfold F_2516 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2513 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2519). clear Hind.
assert (HFabs1 : fst (F_2519 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 117. unfold snd. unfold F_2519. unfold F_2513. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2513. unfold fst in HFabs1. unfold F_2519 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2516 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_2522). clear Hind.
assert (HFabs1 : fst (F_2522 u9 u2 u3 u4 u5 u6 0 0)).
apply Res. trivial_in 116. unfold snd. unfold F_2522. unfold F_2516. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2516. unfold fst in HFabs1. unfold F_2522 in HFabs1.   
pattern u2, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 2522 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
unfold fst. unfold F_2522. specialize true_159 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 2519 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (H: ((le (time (C u5 u8)) u3) = true) \/ ((le (time (C u5 u8)) u3) = false)). 

destruct ((le (time (C u5 u8)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_2596). clear Hind.
assert (HFabs0 : fst (F_2596 u9 u2 u3 u5 u6 u8 0 0)).
apply H1. trivial_in 119. unfold snd. unfold F_2596. unfold F_2519. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2519. unfold F_2596. unfold fst in HFabs0. unfold F_2596 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u3.
pattern u9.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_2600). clear Hind.
assert (HFabs0 : fst (F_2600 u9 u2 u3 u5 u6 u8 0 0)).
apply H1. trivial_in 118. unfold snd. unfold F_2600. unfold F_2519. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2519. unfold F_2600. unfold fst in HFabs0. unfold F_2600 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u3.
pattern u9.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 2600 ] *)

unfold fst. unfold F_2600.
auto.



	(* REWRITING on [ 2596 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2603). clear Hind.
assert (HFabs1 : fst (F_2603 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 120. unfold snd. unfold F_2603. unfold F_2596. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2596. unfold fst in HFabs1. unfold F_2603 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2603 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2606). clear Hind.
assert (HFabs1 : fst (F_2606 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 121. unfold snd. unfold F_2606. unfold F_2603. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2603. unfold fst in HFabs1. unfold F_2606 in HFabs1.   
pattern u5, u8. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 2606 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
unfold fst. unfold F_2606. specialize true_159 with (u1 := u5) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 2432 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (H: ((le (time (C u2 u4)) u3) = true) \/ ((le (time (C u2 u4)) u3) = false)). 

destruct ((le (time (C u2 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_2642). clear Hind.
assert (HFabs0 : fst (F_2642 u9 u2 u3 u4 u5 u6 u8 0)).
apply H1. trivial_in 123. unfold snd. unfold F_2642. unfold F_2432. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2432. unfold F_2642. unfold fst in HFabs0. unfold F_2642 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_2646). clear Hind.
assert (HFabs0 : fst (F_2646 u9 u2 u3 u4 u5 u6 u8 0)).
apply H1. trivial_in 124. unfold snd. unfold F_2646. unfold F_2432. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2432. unfold F_2646. unfold fst in HFabs0. unfold F_2646 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 2642 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2649). clear Hind.
assert (HFabs1 : fst (F_2649 u9 u2 u3 u4 u5 u6 u8 0)).
apply Res. trivial_in 125. unfold snd. unfold F_2649. unfold F_2642. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2642. unfold fst in HFabs1. unfold F_2649 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2646 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2652). clear Hind.
assert (HFabs1 : fst (F_2652 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 127. unfold snd. unfold F_2652. unfold F_2646. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2646. unfold fst in HFabs1. unfold F_2652 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2649 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2655). clear Hind.
assert (HFabs1 : fst (F_2655 u9 u2 u3 u4 u5 u6 u8 0)).
apply Res. trivial_in 126. unfold snd. unfold F_2655. unfold F_2649. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2649. unfold fst in HFabs1. unfold F_2655 in HFabs1.   
pattern u2, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 2655 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
unfold fst. unfold F_2655. specialize true_159 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 2652 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (H: ((le (time (C u5 u8)) u3) = true) \/ ((le (time (C u5 u8)) u3) = false)). 

destruct ((le (time (C u5 u8)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_2722). clear Hind.
assert (HFabs0 : fst (F_2722 u9 u2 u3 u5 u6 u8 0 0)).
apply H1. trivial_in 128. unfold snd. unfold F_2722. unfold F_2652. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2652. unfold F_2722. unfold fst in HFabs0. unfold F_2722 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u3.
pattern u9.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_2726). clear Hind.
assert (HFabs0 : fst (F_2726 u9 u2 u3 u5 u6 u8 0 0)).
apply H1. trivial_in 129. unfold snd. unfold F_2726. unfold F_2652. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2652. unfold F_2726. unfold fst in HFabs0. unfold F_2726 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u3.
pattern u9.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 2722 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2729). clear Hind.
assert (HFabs1 : fst (F_2729 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 130. unfold snd. unfold F_2729. unfold F_2722. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2722. unfold fst in HFabs1. unfold F_2729 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2726 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2732). clear Hind.
assert (HFabs1 : fst (F_2732 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 132. unfold snd. unfold F_2732. unfold F_2726. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2726. unfold fst in HFabs1. unfold F_2732 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 2729 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_2735). clear Hind.
assert (HFabs1 : fst (F_2735 u9 u2 u3 u5 u6 u8 0 0)).
apply Res. trivial_in 131. unfold snd. unfold F_2735. unfold F_2729. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_2729. unfold fst in HFabs1. unfold F_2735 in HFabs1.   
pattern u5, u8. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 2735 ] *)

unfold fst. unfold F_2735.
auto.



	(* SUBSUMPTION on [ 2732 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into _u8. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
unfold fst. unfold F_2732. specialize true_159 with (u1 := u5) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_276 := fun f => exists F, In F LF_276 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, exists e7, exists e8, f = F e1 e2 e3 e4 e5 e6 e7 e8.

Theorem all_true_276: forall F, In F LF_276 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, forall u7: nat, forall u8: nat, fst (F u1 u2  u3  u4  u5  u6  u7  u8).
Proof.
let n := constr:(8) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_276);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_276;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_276: forall (u1: PLAN) (u2: nat) (u3: nat) (u4: nat), (sortedT u1) = true -> (le u2 u3) = false -> (progAt (insAt u1 u2 u4) u3) = (progAt u1 u3).
Proof.
do 4 intro.
apply (all_true_276 F_276);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
