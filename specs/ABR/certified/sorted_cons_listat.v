
Require Import sorted_cons_listat_spec.



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


Hypothesis true_154: forall u1 u2 u3, (le u1 u2) = true -> (le u3 u1) = true -> (le u3 u2) = false -> False.

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


Definition type_LF_276 :=  PLAN ->  nat ->  nat ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_276 : type_LF_276:= (fun   u1 u2 u3 _ _ _ _ => ((sortedT u1) = true -> (listAt u1 u2) = Nil -> (le u3 u2) = true -> (listAt u1 u3) = Nil, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_listAt ((model_PLAN u1):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((model_PLAN u1):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_328 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => (false = true -> (listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = false -> (listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u3) = Nil, (Term id_false nil)::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_false nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_310 : type_LF_276:= (fun    _ u2 u3 _ _ _ _ => (true = true -> (listAt Nil u2) = Nil -> (le u3 u2) = true -> (listAt Nil u3) = Nil, (Term id_true nil)::(Term id_true nil)::(Term id_listAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Nil nil):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_316 : type_LF_276:= (fun    _ u2 u3 u5 u6 _ _ => (true = true -> (listAt (Cons (C u5 u6) Nil) u2) = Nil -> (le u3 u2) = true -> (listAt (Cons (C u5 u6) Nil) u3) = Nil, (Term id_true nil)::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_329 : type_LF_276:= (fun    _ u2 u3 _ _ _ _ => ((listAt Nil u2) = Nil -> (le u3 u2) = true -> (listAt Nil u3) = Nil, (Term id_listAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Nil nil):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_333 : type_LF_276:= (fun    _ u2 u3 _ _ _ _ => ((listAt Nil u2) = Nil -> (le u3 u2) = true -> Nil = Nil, (Term id_listAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_Nil nil)::(Term id_Nil nil)::nil)).
Definition F_322 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((sortedT (Cons (C u4 u7) u8)) = true -> (listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u3) = Nil, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_372 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) (time (C u4 u7))) = true -> (listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u3) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (Term id_time ((Term id_C ((model_nat u4):: (model_nat u7)::nil))::nil))::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_330 : type_LF_276:= (fun    _ u2 u3 u5 u6 _ _ => ((listAt (Cons (C u5 u6) Nil) u2) = Nil -> (le u3 u2) = true -> (listAt (Cons (C u5 u6) Nil) u3) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_413 : type_LF_276:= (fun    _ u2 u3 u5 u6 _ _ => ((listAt (Cons (C u5 u6) Nil) u2) = Nil -> (le u3 u2) = true -> (le (time (C u5 u6)) u3) = true -> (Cons (C u5 u6) Nil) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil))::(Term id_Nil nil)::nil)).
Definition F_417 : type_LF_276:= (fun    _ u2 u3 u5 u6 _ _ => ((listAt (Cons (C u5 u6) Nil) u2) = Nil -> (le u3 u2) = true -> (le (time (C u5 u6)) u3) = false -> (listAt Nil u3) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_listAt ((Term id_Nil nil):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_423 : type_LF_276:= (fun    _ u2 u3 u5 u6 _ _ => ((listAt (Cons (C u5 u6) Nil) u2) = Nil -> (le u3 u2) = true -> (le (time (C u5 u6)) u3) = false -> Nil = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_Nil nil)::(Term id_Nil nil)::nil)).
Definition F_375 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u3) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_455 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le (time (C u5 u6)) u3) = true -> (Cons (C u5 u6) (Cons (C u4 u7) u8)) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_Nil nil)::nil)).
Definition F_459 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le (time (C u5 u6)) u3) = false -> (listAt (Cons (C u4 u7) u8) u3) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil)):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_420 : type_LF_276:= (fun    _ u2 u3 u5 u6 _ _ => ((listAt (Cons (C u5 u6) Nil) u2) = Nil -> (le u3 u2) = true -> (le u5 u3) = true -> (Cons (C u5 u6) Nil) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil))::(Term id_Nil nil)::nil)).
Definition F_523 : type_LF_276:= (fun    _ u2 u3 u5 u6 _ _ => ((Cons (C u5 u6) Nil) = Nil -> (le u3 u2) = true -> (le u5 u3) = true -> (le (time (C u5 u6)) u2) = true -> (Cons (C u5 u6) Nil) = Nil, (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil))::(Term id_Nil nil)::nil)).
Definition F_527 : type_LF_276:= (fun    _ u2 u3 u5 u6 _ _ => ((listAt Nil u2) = Nil -> (le u3 u2) = true -> (le u5 u3) = true -> (le (time (C u5 u6)) u2) = false -> (Cons (C u5 u6) Nil) = Nil, (Term id_listAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil))::(Term id_Nil nil)::nil)).
Definition F_530 : type_LF_276:= (fun    _ u2 u3 u5 u6 _ _ => (Nil = Nil -> (le u3 u2) = true -> (le u5 u3) = true -> (le (time (C u5 u6)) u2) = false -> (Cons (C u5 u6) Nil) = Nil, (Term id_Nil nil)::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil))::(Term id_Nil nil)::nil)).
Definition F_531 : type_LF_276:= (fun    _ u2 u3 u5 u6 _ _ => ((le u3 u2) = true -> (le u5 u3) = true -> (le (time (C u5 u6)) u2) = false -> (Cons (C u5 u6) Nil) = Nil, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil))::(Term id_Nil nil)::nil)).
Definition F_534 : type_LF_276:= (fun    _ u2 u3 u5 u6 _ _ => ((le u3 u2) = true -> (le u5 u3) = true -> (le u5 u2) = false -> (Cons (C u5 u6) Nil) = Nil, (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Nil nil)::nil))::(Term id_Nil nil)::nil)).
Definition F_462 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = true -> (Cons (C u5 u6) (Cons (C u4 u7) u8)) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_Nil nil)::nil)).
Definition F_577 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((Cons (C u5 u6) (Cons (C u4 u7) u8)) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = true -> (le (time (C u5 u6)) u2) = true -> (Cons (C u5 u6) (Cons (C u4 u7) u8)) = Nil, (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_Nil nil)::nil)).
Definition F_581 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u4 u7) u8) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = true -> (le (time (C u5 u6)) u2) = false -> (Cons (C u5 u6) (Cons (C u4 u7) u8)) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_Nil nil)::nil)).
Definition F_584 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u4 u7) u8) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = true -> (le u5 u2) = false -> (Cons (C u5 u6) (Cons (C u4 u7) u8)) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_Nil nil)::nil)).
Definition F_465 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (listAt (Cons (C u4 u7) u8) u3) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil)):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_619 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le (time (C u4 u7)) u3) = true -> (Cons (C u4 u7) u8) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::(Term id_Nil nil)::nil)).
Definition F_623 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le (time (C u4 u7)) u3) = false -> (listAt u8 u3) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u7)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_listAt ((model_PLAN u8):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_626 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = true -> (Cons (C u4 u7) u8) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::(Term id_Nil nil)::nil)).
Definition F_685 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((Cons (C u5 u6) (Cons (C u4 u7) u8)) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = true -> (le (time (C u5 u6)) u2) = true -> (Cons (C u4 u7) u8) = Nil, (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::(Term id_Nil nil)::nil)).
Definition F_689 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u4 u7) u8) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = true -> (le (time (C u5 u6)) u2) = false -> (Cons (C u4 u7) u8) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::(Term id_Nil nil)::nil)).
Definition F_629 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u5 u6) (Cons (C u4 u7) u8)) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = false -> (listAt u8 u3) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_listAt ((model_PLAN u8):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_726 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((Cons (C u5 u6) (Cons (C u4 u7) u8)) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = false -> (le (time (C u5 u6)) u2) = true -> (listAt u8 u3) = Nil, (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u6)::nil)):: (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((model_PLAN u8):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_730 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u6 u7 => ((listAt (Cons (C u4 u7) u8) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = false -> (le (time (C u5 u6)) u2) = false -> (listAt u8 u3) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u6)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_listAt ((model_PLAN u8):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_692 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u7 _ => ((listAt (Cons (C u4 u7) u8) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = true -> (le u5 u2) = false -> (Cons (C u4 u7) u8) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::(Term id_Nil nil)::nil)).
Definition F_769 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u7 _ => ((Cons (C u4 u7) u8) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = true -> (le u5 u2) = false -> (le (time (C u4 u7)) u2) = true -> (Cons (C u4 u7) u8) = Nil, (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::(Term id_Nil nil)::nil)).
Definition F_773 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u7 _ => ((listAt u8 u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = true -> (le u5 u2) = false -> (le (time (C u4 u7)) u2) = false -> (Cons (C u4 u7) u8) = Nil, (Term id_listAt ((model_PLAN u8):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::(Term id_Nil nil)::nil)).
Definition F_776 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u7 _ => ((listAt u8 u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = true -> (le u5 u2) = false -> (le u4 u2) = false -> (Cons (C u4 u7) u8) = Nil, (Term id_listAt ((model_PLAN u8):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::(Term id_Nil nil)::nil)).
Definition F_733 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u7 _ => ((listAt (Cons (C u4 u7) u8) u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = false -> (le u5 u2) = false -> (listAt u8 u3) = Nil, (Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil)):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_listAt ((model_PLAN u8):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_811 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u7 _ => ((Cons (C u4 u7) u8) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = false -> (le u5 u2) = false -> (le (time (C u4 u7)) u2) = true -> (listAt u8 u3) = Nil, (Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((model_PLAN u8):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).
Definition F_815 : type_LF_276:= (fun   u8 u2 u3 u4 u5 u7 _ => ((listAt u8 u2) = Nil -> (le u3 u2) = true -> (le u4 u5) = true -> (sortedT u8) = true -> (le (timel u8) u4) = true -> (le u5 u3) = false -> (le u4 u3) = false -> (le u5 u2) = false -> (le (time (C u4 u7)) u2) = false -> (listAt u8 u3) = Nil, (Term id_listAt ((model_PLAN u8):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u8)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u8)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u4):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_listAt ((model_PLAN u8):: (model_nat u3)::nil))::(Term id_Nil nil)::nil)).

Definition LF_276 := [F_276, F_328, F_310, F_316, F_329, F_333, F_322, F_372, F_330, F_413, F_417, F_423, F_375, F_455, F_459, F_420, F_523, F_527, F_530, F_531, F_534, F_462, F_577, F_581, F_584, F_465, F_619, F_623, F_626, F_685, F_689, F_629, F_726, F_730, F_692, F_769, F_773, F_776, F_733, F_811, F_815].


Function f_276 (u1: PLAN) {struct u1} : bool :=
 match u1 with
| Nil => true
| (Cons (C u5 u6) Nil) => true
| (Cons (C u5 u6) (Cons (C u4 u7) u8)) => true
end.

Lemma main_276 : forall F, In F LF_276 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, forall u7, (forall F', In F' LF_276 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, forall e7, less (snd (F' e1 e2 e3 e4 e5 e6 e7)) (snd (F u1 u2 u3 u4 u5 u6 u7)) -> fst (F' e1 e2 e3 e4 e5 e6 e7)) -> fst (F u1 u2 u3 u4 u5 u6 u7).
Proof.
intros F HF u1 u2 u3 u4 u5 u6 u7; case_In HF; intro Hind.

	(* GENERATE on [ 276 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. 

revert Hind.

pattern u1, (f_276 u1). apply f_276_ind.

(* case [ 310 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_310). clear HFabs0.
assert (HFabs0 : fst (F_310 Nil u2 u3 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_310. unfold F_276. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_276. unfold F_310.
auto.


(* case [ 316 ] *)

intros _u1. intro u5. intro u6.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_316). clear HFabs0.
assert (HFabs0 : fst (F_316 Nil u2 u3 u5 u6 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_316. unfold F_276. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_276. unfold F_316.
auto.



intros _u1. intro u5. intro u6. intro u4. intro u7. intro u8.  intro eq_1.  intro HFabs0.
case_eq (le u4 u5); [intro H | intro H].

(* case [ 322 ] *)

assert (Hind := HFabs0 F_322). clear HFabs0.
assert (HFabs0 : fst (F_322 u8 u2 u3 u4 u5 u6 u7)).
apply Hind. trivial_in 6. unfold snd. unfold F_322. unfold F_276. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_276. unfold F_322. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 328 ] *)

assert (Hind := HFabs0 F_328). clear HFabs0.
assert (HFabs0 : fst (F_328 u8 u2 u3 u4 u5 u6 u7)).
apply Hind. trivial_in 1. unfold snd. unfold F_328. unfold F_276. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_276. unfold F_328. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 328 ] *)

unfold fst. unfold F_328. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 310 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. 
rename _u2 into u2. rename _u3 into u3. 
assert (H := Hind F_329). 
assert (HFabs0 : fst (F_329 Nil u2 u3 0 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_329. unfold F_310. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_310. unfold F_329.

unfold fst in HFabs0. unfold F_329 in HFabs0.
auto.



	(* NEGATIVE DECOMPOSITION on [ 316 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. 
assert (H := Hind F_330). 
assert (HFabs0 : fst (F_330 Nil u2 u3 u5 u6 0 0)).
apply H. trivial_in 8. unfold snd. unfold F_330. unfold F_316. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_316. unfold F_330.

unfold fst in HFabs0. unfold F_330 in HFabs0.
auto.



	(* REWRITING on [ 329 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_333). clear Hind.
assert (HFabs1 : fst (F_333 Nil u2 u3 0 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_333. unfold F_329. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_329. unfold fst in HFabs1. unfold F_333 in HFabs1.   
pattern u3. simpl (listAt _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 333 ] *)

unfold fst. unfold F_333.
auto.



	(* AUGMENTATION on [ 322 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (H := Hind F_372). clear Hind.
assert (HFabs0: fst (F_372 u8 u2 u3 u4 u5 u6 u7)).
apply H. trivial_in 7. unfold snd. unfold F_322. unfold F_372. rewrite_model. abstract solve_rpo_mul.

unfold fst. unfold F_322.

specialize true_231 with (u1 := (C u4 u7)) (u2 := u8).
specialize true_199 with (u1 := (C u4 u7)) (u2 := u8). auto.




	(* REWRITING on [ 372 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_375). clear Hind.
assert (HFabs1 : fst (F_375 u8 u2 u3 u4 u5 u6 u7)).
apply Res. trivial_in 12. unfold snd. unfold F_375. unfold F_372. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_372. unfold fst in HFabs1. unfold F_375 in HFabs1.   
pattern u4, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 330 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. 
assert (H: ((le (time (C u5 u6)) u3) = true) \/ ((le (time (C u5 u6)) u3) = false)). 

destruct ((le (time (C u5 u6)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 146 ] *)

assert (H1 := Hind F_413). clear Hind.
assert (HFabs0 : fst (F_413 Nil u2 u3 u5 u6 0 0)).
apply H1. trivial_in 9. unfold snd. unfold F_413. unfold F_330. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_330. unfold F_413. unfold fst in HFabs0. unfold F_413 in HFabs0. simpl in HFabs0. 
pattern (C u5 u6).
pattern u3.
pattern Nil.
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 147 ] *)

assert (H1 := Hind F_417). clear Hind.
assert (HFabs0 : fst (F_417 Nil u2 u3 u5 u6 0 0)).
apply H1. trivial_in 10. unfold snd. unfold F_417. unfold F_330. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_330. unfold F_417. unfold fst in HFabs0. unfold F_417 in HFabs0. simpl in HFabs0. 
pattern (C u5 u6).
pattern u3.
pattern Nil.
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 413 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_420). clear Hind.
assert (HFabs1 : fst (F_420 Nil u2 u3 u5 u6 0 0)).
apply Res. trivial_in 15. unfold snd. unfold F_420. unfold F_413. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_413. unfold fst in HFabs1. unfold F_420 in HFabs1.   
pattern u5, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 417 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_423). clear Hind.
assert (HFabs1 : fst (F_423 Nil u2 u3 u5 u6 0 0)).
apply Res. trivial_in 11. unfold snd. unfold F_423. unfold F_417. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_417. unfold fst in HFabs1. unfold F_423 in HFabs1.   
pattern u3. simpl (listAt _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 423 ] *)

unfold fst. unfold F_423.
auto.



	(* TOTAL CASE REWRITING on [ 375 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u5 u6)) u3) = true) \/ ((le (time (C u5 u6)) u3) = false)). 

destruct ((le (time (C u5 u6)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 146 ] *)

assert (H1 := Hind F_455). clear Hind.
assert (HFabs0 : fst (F_455 u8 u2 u3 u4 u5 u6 u7)).
apply H1. trivial_in 13. unfold snd. unfold F_455. unfold F_375. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_375. unfold F_455. unfold fst in HFabs0. unfold F_455 in HFabs0. simpl in HFabs0. 
pattern (C u5 u6).
pattern u3.
pattern (Cons (C u4 u7) u8).
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 147 ] *)

assert (H1 := Hind F_459). clear Hind.
assert (HFabs0 : fst (F_459 u8 u2 u3 u4 u5 u6 u7)).
apply H1. trivial_in 14. unfold snd. unfold F_459. unfold F_375. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_375. unfold F_459. unfold fst in HFabs0. unfold F_459 in HFabs0. simpl in HFabs0. 
pattern (C u5 u6).
pattern u3.
pattern (Cons (C u4 u7) u8).
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 455 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_462). clear Hind.
assert (HFabs1 : fst (F_462 u8 u2 u3 u4 u5 u6 u7)).
apply Res. trivial_in 21. unfold snd. unfold F_462. unfold F_455. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_455. unfold fst in HFabs1. unfold F_462 in HFabs1.   
pattern u5, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 459 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_465). clear Hind.
assert (HFabs1 : fst (F_465 u8 u2 u3 u4 u5 u6 u7)).
apply Res. trivial_in 25. unfold snd. unfold F_465. unfold F_459. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_459. unfold fst in HFabs1. unfold F_465 in HFabs1.   
pattern u5, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 420 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. 
assert (H: ((le (time (C u5 u6)) u2) = true) \/ ((le (time (C u5 u6)) u2) = false)). 

destruct ((le (time (C u5 u6)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 146 ] *)

assert (H1 := Hind F_523). clear Hind.
assert (HFabs0 : fst (F_523 Nil u2 u3 u5 u6 0 0)).
apply H1. trivial_in 16. unfold snd. unfold F_523. unfold F_420. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_420. unfold F_523. unfold fst in HFabs0. unfold F_523 in HFabs0. simpl in HFabs0. 
pattern (C u5 u6).
pattern u2.
pattern Nil.
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 147 ] *)

assert (H1 := Hind F_527). clear Hind.
assert (HFabs0 : fst (F_527 Nil u2 u3 u5 u6 0 0)).
apply H1. trivial_in 17. unfold snd. unfold F_527. unfold F_420. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_420. unfold F_527. unfold fst in HFabs0. unfold F_527 in HFabs0. simpl in HFabs0. 
pattern (C u5 u6).
pattern u2.
pattern Nil.
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 523 ] *)

unfold fst. unfold F_523.
auto.



	(* REWRITING on [ 527 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_530). clear Hind.
assert (HFabs1 : fst (F_530 Nil u2 u3 u5 u6 0 0)).
apply Res. trivial_in 18. unfold snd. unfold F_530. unfold F_527. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_527. unfold fst in HFabs1. unfold F_530 in HFabs1.   
pattern u2. simpl (listAt _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE DECOMPOSITION on [ 530 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. 
assert (H := Hind F_531). 
assert (HFabs0 : fst (F_531 Nil u2 u3 u5 u6 0 0)).
apply H. trivial_in 19. unfold snd. unfold F_531. unfold F_530. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_530. unfold F_531.

unfold fst in HFabs0. unfold F_531 in HFabs0.
auto.



	(* REWRITING on [ 531 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_534). clear Hind.
assert (HFabs1 : fst (F_534 Nil u2 u3 u5 u6 0 0)).
apply Res. trivial_in 20. unfold snd. unfold F_534. unfold F_531. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_531. unfold fst in HFabs1. unfold F_534 in HFabs1.   
pattern u5, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 534 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. 
rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. rename _u6 into u6. 
unfold fst. unfold F_534. specialize true_154 with (u1 := u3) (u2 := u2) (u3 := u5). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 462 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u5 u6)) u2) = true) \/ ((le (time (C u5 u6)) u2) = false)). 

destruct ((le (time (C u5 u6)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 146 ] *)

assert (H1 := Hind F_577). clear Hind.
assert (HFabs0 : fst (F_577 u8 u2 u3 u4 u5 u6 u7)).
apply H1. trivial_in 22. unfold snd. unfold F_577. unfold F_462. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_462. unfold F_577. unfold fst in HFabs0. unfold F_577 in HFabs0. simpl in HFabs0. 
pattern (C u5 u6).
pattern u2.
pattern (Cons (C u4 u7) u8).
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 147 ] *)

assert (H1 := Hind F_581). clear Hind.
assert (HFabs0 : fst (F_581 u8 u2 u3 u4 u5 u6 u7)).
apply H1. trivial_in 23. unfold snd. unfold F_581. unfold F_462. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_462. unfold F_581. unfold fst in HFabs0. unfold F_581 in HFabs0. simpl in HFabs0. 
pattern (C u5 u6).
pattern u2.
pattern (Cons (C u4 u7) u8).
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 577 ] *)

unfold fst. unfold F_577.
auto.



	(* REWRITING on [ 581 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_584). clear Hind.
assert (HFabs1 : fst (F_584 u8 u2 u3 u4 u5 u6 u7)).
apply Res. trivial_in 24. unfold snd. unfold F_584. unfold F_581. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_581. unfold fst in HFabs1. unfold F_584 in HFabs1.   
pattern u5, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 584 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
unfold fst. unfold F_584. specialize true_154 with (u1 := u3) (u2 := u2) (u3 := u5). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 465 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u4 u7)) u3) = true) \/ ((le (time (C u4 u7)) u3) = false)). 

destruct ((le (time (C u4 u7)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 146 ] *)

assert (H1 := Hind F_619). clear Hind.
assert (HFabs0 : fst (F_619 u8 u2 u3 u4 u5 u6 u7)).
apply H1. trivial_in 26. unfold snd. unfold F_619. unfold F_465. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_465. unfold F_619. unfold fst in HFabs0. unfold F_619 in HFabs0. simpl in HFabs0. 
pattern (C u4 u7).
pattern u3.
pattern u8.
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 147 ] *)

assert (H1 := Hind F_623). clear Hind.
assert (HFabs0 : fst (F_623 u8 u2 u3 u4 u5 u6 u7)).
apply H1. trivial_in 27. unfold snd. unfold F_623. unfold F_465. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_465. unfold F_623. unfold fst in HFabs0. unfold F_623 in HFabs0. simpl in HFabs0. 
pattern (C u4 u7).
pattern u3.
pattern u8.
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 619 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_626). clear Hind.
assert (HFabs1 : fst (F_626 u8 u2 u3 u4 u5 u6 u7)).
apply Res. trivial_in 28. unfold snd. unfold F_626. unfold F_619. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_619. unfold fst in HFabs1. unfold F_626 in HFabs1.   
pattern u4, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 623 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_629). clear Hind.
assert (HFabs1 : fst (F_629 u8 u2 u3 u4 u5 u6 u7)).
apply Res. trivial_in 31. unfold snd. unfold F_629. unfold F_623. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_623. unfold fst in HFabs1. unfold F_629 in HFabs1.   
pattern u4, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 626 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u5 u6)) u2) = true) \/ ((le (time (C u5 u6)) u2) = false)). 

destruct ((le (time (C u5 u6)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 146 ] *)

assert (H1 := Hind F_685). clear Hind.
assert (HFabs0 : fst (F_685 u8 u2 u3 u4 u5 u6 u7)).
apply H1. trivial_in 29. unfold snd. unfold F_685. unfold F_626. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_626. unfold F_685. unfold fst in HFabs0. unfold F_685 in HFabs0. simpl in HFabs0. 
pattern (C u5 u6).
pattern u2.
pattern (Cons (C u4 u7) u8).
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 147 ] *)

assert (H1 := Hind F_689). clear Hind.
assert (HFabs0 : fst (F_689 u8 u2 u3 u4 u5 u6 u7)).
apply H1. trivial_in 30. unfold snd. unfold F_689. unfold F_626. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_626. unfold F_689. unfold fst in HFabs0. unfold F_689 in HFabs0. simpl in HFabs0. 
pattern (C u5 u6).
pattern u2.
pattern (Cons (C u4 u7) u8).
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 685 ] *)

unfold fst. unfold F_685. intros. try discriminate.



	(* REWRITING on [ 689 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_692). clear Hind.
assert (HFabs1 : fst (F_692 u8 u2 u3 u4 u5 u7 0)).
apply Res. trivial_in 34. unfold snd. unfold F_692. unfold F_689. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_689. unfold fst in HFabs1. unfold F_692 in HFabs1.   
pattern u5, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 629 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u5 u6)) u2) = true) \/ ((le (time (C u5 u6)) u2) = false)). 

destruct ((le (time (C u5 u6)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 146 ] *)

assert (H1 := Hind F_726). clear Hind.
assert (HFabs0 : fst (F_726 u8 u2 u3 u4 u5 u6 u7)).
apply H1. trivial_in 32. unfold snd. unfold F_726. unfold F_629. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_629. unfold F_726. unfold fst in HFabs0. unfold F_726 in HFabs0. simpl in HFabs0. 
pattern (C u5 u6).
pattern u2.
pattern (Cons (C u4 u7) u8).
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 147 ] *)

assert (H1 := Hind F_730). clear Hind.
assert (HFabs0 : fst (F_730 u8 u2 u3 u4 u5 u6 u7)).
apply H1. trivial_in 33. unfold snd. unfold F_730. unfold F_629. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_629. unfold F_730. unfold fst in HFabs0. unfold F_730 in HFabs0. simpl in HFabs0. 
pattern (C u5 u6).
pattern u2.
pattern (Cons (C u4 u7) u8).
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 726 ] *)

unfold fst. unfold F_726. intros. try discriminate.



	(* REWRITING on [ 730 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_733). clear Hind.
assert (HFabs1 : fst (F_733 u8 u2 u3 u4 u5 u7 0)).
apply Res. trivial_in 38. unfold snd. unfold F_733. unfold F_730. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_730. unfold fst in HFabs1. unfold F_733 in HFabs1.   
pattern u5, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 692 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u7. rename u7 into d_u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u7 into u7. 
assert (H: ((le (time (C u4 u7)) u2) = true) \/ ((le (time (C u4 u7)) u2) = false)). 

destruct ((le (time (C u4 u7)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 146 ] *)

assert (H1 := Hind F_769). clear Hind.
assert (HFabs0 : fst (F_769 u8 u2 u3 u4 u5 u7 0)).
apply H1. trivial_in 35. unfold snd. unfold F_769. unfold F_692. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_692. unfold F_769. unfold fst in HFabs0. unfold F_769 in HFabs0. simpl in HFabs0. 
pattern (C u4 u7).
pattern u2.
pattern u8.
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 147 ] *)

assert (H1 := Hind F_773). clear Hind.
assert (HFabs0 : fst (F_773 u8 u2 u3 u4 u5 u7 0)).
apply H1. trivial_in 36. unfold snd. unfold F_773. unfold F_692. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_692. unfold F_773. unfold fst in HFabs0. unfold F_773 in HFabs0. simpl in HFabs0. 
pattern (C u4 u7).
pattern u2.
pattern u8.
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 769 ] *)

unfold fst. unfold F_769.
auto.



	(* REWRITING on [ 773 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u7. rename u7 into d_u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u7 into u7. 
assert (Res := Hind F_776). clear Hind.
assert (HFabs1 : fst (F_776 u8 u2 u3 u4 u5 u7 0)).
apply Res. trivial_in 37. unfold snd. unfold F_776. unfold F_773. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_773. unfold fst in HFabs1. unfold F_776 in HFabs1.   
pattern u4, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 776 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u7. rename u7 into d_u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u7 into u7. 
unfold fst. unfold F_776. specialize true_154 with (u1 := u3) (u2 := u2) (u3 := u4). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 733 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u7. rename u7 into d_u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u7 into u7. 
assert (H: ((le (time (C u4 u7)) u2) = true) \/ ((le (time (C u4 u7)) u2) = false)). 

destruct ((le (time (C u4 u7)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 146 ] *)

assert (H1 := Hind F_811). clear Hind.
assert (HFabs0 : fst (F_811 u8 u2 u3 u4 u5 u7 0)).
apply H1. trivial_in 39. unfold snd. unfold F_811. unfold F_733. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_733. unfold F_811. unfold fst in HFabs0. unfold F_811 in HFabs0. simpl in HFabs0. 
pattern (C u4 u7).
pattern u2.
pattern u8.
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 147 ] *)

assert (H1 := Hind F_815). clear Hind.
assert (HFabs0 : fst (F_815 u8 u2 u3 u4 u5 u7 0)).
apply H1. trivial_in 40. unfold snd. unfold F_815. unfold F_733. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_733. unfold F_815. unfold fst in HFabs0. unfold F_815 in HFabs0. simpl in HFabs0. 
pattern (C u4 u7).
pattern u2.
pattern u8.
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 811 ] *)

unfold fst. unfold F_811. intros. try discriminate.



	(* REWRITING on [ 815 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u7. rename u7 into d_u7. 
rename _u8 into u8. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u7 into u7. 
assert (Res := Hind F_276). clear Hind.
assert (HFabs1 : fst (F_276 u8 u2 u3 0 0 0 0)).
apply Res. trivial_in 0. unfold snd. unfold F_276. unfold F_815. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_815. unfold fst in HFabs1. unfold F_276 in HFabs1.   
pattern u4, u7. simpl (time _). cbv beta.
 simpl. auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_276 := fun f => exists F, In F LF_276 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, exists e7, f = F e1 e2 e3 e4 e5 e6 e7.

Theorem all_true_276: forall F, In F LF_276 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, forall u7: nat, fst (F u1 u2  u3  u4  u5  u6  u7).
Proof.
let n := constr:(7) in
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


Theorem true_276: forall (u1: PLAN) (u2: nat) (u3: nat), (sortedT u1) = true -> (listAt u1 u2) = Nil -> (le u3 u2) = true -> (listAt u1 u3) = Nil.
Proof.
do 3 intro.
apply (all_true_276 F_276);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
