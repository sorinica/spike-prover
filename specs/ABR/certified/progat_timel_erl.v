
Require Import progat_timel_erl_spec.



Definition type_LF_158 :=  nat -> (Prop * (List.list term)).

Definition F_158 : type_LF_158:= (fun    u1 => ((le u1 u1) = false -> False, (Term id_le ((model_nat u1):: (model_nat u1)::nil))::(Term id_false nil)::nil)).
Definition F_169 : type_LF_158:= (fun     _ => (true = false -> False, (Term id_true nil)::(Term id_false nil)::nil)).

Definition LF_158 := [F_158, F_169].


Function f_158 (u1: nat) {struct u1} : bool :=
 match u1 with
| 0 => true
| (S u2) => true
end.

Lemma main_158 : forall F, In F LF_158 -> forall u1, (forall F', In F' LF_158 -> forall e1, less (snd (F' e1)) (snd (F u1)) -> fst (F' e1)) -> fst (F u1).
Proof.
intros F HF u1; case_In HF; intro Hind.

	(* GENERATE on [ 158 ] *)

rename u1 into _u1. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_158 u1). apply f_158_ind.

(* case [ 169 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_169). clear HFabs0.
assert (HFabs0 : fst (F_169 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_169. unfold F_158. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_158. unfold F_169.
auto.


(* case [ 175 ] *)

intros _u1. intro u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_158). clear HFabs0.
assert (HFabs0 : fst (F_158 u2)).
apply Hind. trivial_in 0. unfold snd. unfold F_158. unfold F_158. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_158. unfold F_158.
auto.





	(* NEGATIVE CLASH on [ 169 ] *)

unfold fst. unfold F_169. intros. try discriminate.



Qed.



(* the set of all formula instances from the proof *)
Definition S_158 := fun f => exists F, In F LF_158 /\ exists e1, f = F e1.

Theorem all_true_158: forall F, In F LF_158 -> forall u1: nat, fst (F u1).
Proof.
let n := constr:(1) in
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


Theorem true_158: forall (u1: nat), (le u1 u1) = false -> False.
Proof.
do 1 intro.
apply (all_true_158 F_158);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_179 :=  PLAN ->  OBJ ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_179 : type_LF_179:= (fun  u2 u1  _ _ _ => ((sortedT (Cons u1 u2)) = true -> (sortedT u2) = true, (Term id_sortedT ((Term id_Cons ((model_OBJ u1):: (model_PLAN u2)::nil))::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u2)::nil))::(Term id_true nil)::nil)).
Definition F_199 : type_LF_179:= (fun  u7  _ u3 u4 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (sortedT (Cons (C u3 u6) u7)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_205 : type_LF_179:= (fun  u7  _ u3 u4 u6 => (false = true -> (le u3 u4) = false -> (sortedT (Cons (C u3 u6) u7)) = true, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_193 : type_LF_179:= (fun   _  _  _ _ _ => (true = true -> (sortedT Nil) = true, (Term id_true nil)::(Term id_true nil)::(Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_206 : type_LF_179:= (fun   _  _  _ _ _ => ((sortedT Nil) = true, (Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_209 : type_LF_179:= (fun   _  _  _ _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).

Definition LF_179 := [F_179, F_199, F_205, F_193, F_206, F_209].


Function f_179 (u2: PLAN) (u1: OBJ) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons (C u3 u6) u7), (C u4 u5) => true
end.

Lemma main_179 : forall F, In F LF_179 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_179 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 179 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_179 u2 u1). apply f_179_ind.

(* case [ 193 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_193). clear HFabs0.
assert (HFabs0 : fst (F_193 Nil (C 0 0 ) 0 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_193. unfold F_179. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_179. unfold F_193.
auto.



intros _u2 _u1. intro u3. intro u6. intro u7.  intro eq_1. intro u4. intro u5.  intro eq_2.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 199 ] *)

assert (Hind := HFabs0 F_199). clear HFabs0.
assert (HFabs0 : fst (F_199 u7 (C 0 0 ) u3 u4 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_199. unfold F_179. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_179. unfold F_199. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 205 ] *)

assert (Hind := HFabs0 F_205). clear HFabs0.
assert (HFabs0 : fst (F_205 u7 (C 0 0 ) u3 u4 u6)).
apply Hind. trivial_in 2. unfold snd. unfold F_205. unfold F_179. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_179. unfold F_205. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* TAUTOLOGY on [ 199 ] *)

unfold fst. unfold F_199.
auto.



	(* NEGATIVE CLASH on [ 205 ] *)

unfold fst. unfold F_205. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 193 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (H := Hind F_206). 
assert (HFabs0 : fst (F_206 Nil (C 0 0 ) 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_206. unfold F_193. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_193. unfold F_206.

unfold fst in HFabs0. unfold F_206 in HFabs0.
auto.



	(* REWRITING on [ 206 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (Res := Hind F_209). clear Hind.
assert (HFabs1 : fst (F_209 Nil (C 0 0 ) 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_209. unfold F_206. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_206. unfold fst in HFabs1. unfold F_209 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 209 ] *)

unfold fst. unfold F_209.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_179 := fun f => exists F, In F LF_179 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_179: forall F, In F LF_179 -> forall u1: PLAN, forall u2: OBJ, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2 u3  u4  u5).
Proof.
let n := constr:(5) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_179);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_179;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_179: forall (u2: PLAN) (u1: OBJ), (sortedT (Cons u1 u2)) = true -> (sortedT u2) = true.
Proof.
do 2 intro.
apply (all_true_179 F_179);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_210 :=  PLAN ->  OBJ ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_210 : type_LF_210:= (fun  u2 u1  _ _ _ _ => ((sortedT (Cons u1 u2)) = true -> (le (timel u2) (time u1)) = true, (Term id_sortedT ((Term id_Cons ((model_OBJ u1):: (model_PLAN u2)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u2)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_237 : type_LF_210:= (fun  u7  _ u3 u4 u5 u6 => (false = true -> (le u3 u4) = false -> (le (timel (Cons (C u3 u6) u7)) (time (C u4 u5))) = true, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_225 : type_LF_210:= (fun   _ u1  _ _ _ _ => (true = true -> (le (timel Nil) (time u1)) = true, (Term id_true nil)::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_231 : type_LF_210:= (fun  u7  _ u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (timel (Cons (C u3 u6) u7)) (time (C u4 u5))) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_238 : type_LF_210:= (fun   _ u1  _ _ _ _ => ((le (timel Nil) (time u1)) = true, (Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_241 : type_LF_210:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (timel (Cons (C u3 u6) u7)) u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_244 : type_LF_210:= (fun   _ u1  _ _ _ _ => ((le 0 (time u1)) = true, (Term id_le ((Term id_0 nil):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_250 : type_LF_210:= (fun   _  _  _ _ _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).
Definition F_247 : type_LF_210:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (time (C u3 u6)) u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u3):: (model_nat u6)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_253 : type_LF_210:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le u3 u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::nil)).

Definition LF_210 := [F_210, F_237, F_225, F_231, F_238, F_241, F_244, F_250, F_247, F_253].


Function f_210 (u2: PLAN) (u1: OBJ) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons (C u3 u6) u7), (C u4 u5) => true
end.

Lemma main_210 : forall F, In F LF_210 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, (forall F', In F' LF_210 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, less (snd (F' e1 e2 e3 e4 e5 e6)) (snd (F u1 u2 u3 u4 u5 u6)) -> fst (F' e1 e2 e3 e4 e5 e6)) -> fst (F u1 u2 u3 u4 u5 u6).
Proof.
intros F HF u1 u2 u3 u4 u5 u6; case_In HF; intro Hind.

	(* GENERATE on [ 210 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_210 u2 u1). apply f_210_ind.

(* case [ 225 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_225). clear HFabs0.
assert (HFabs0 : fst (F_225 Nil _u1 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_225. unfold F_210. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_210. unfold F_225.
auto.



intros _u2 _u1. intro u3. intro u6. intro u7.  intro eq_1. intro u4. intro u5.  intro eq_2.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 231 ] *)

assert (Hind := HFabs0 F_231). clear HFabs0.
assert (HFabs0 : fst (F_231 u7 (C 0 0 ) u3 u4 u5 u6)).
apply Hind. trivial_in 3. unfold snd. unfold F_231. unfold F_210. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_210. unfold F_231. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 237 ] *)

assert (Hind := HFabs0 F_237). clear HFabs0.
assert (HFabs0 : fst (F_237 u7 (C 0 0 ) u3 u4 u5 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_237. unfold F_210. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_210. unfold F_237. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 237 ] *)

unfold fst. unfold F_237. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 225 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (H := Hind F_238). 
assert (HFabs0 : fst (F_238 Nil u1 0 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_238. unfold F_225. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_225. unfold F_238.

unfold fst in HFabs0. unfold F_238 in HFabs0.
auto.



	(* REWRITING on [ 231 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_241). clear Hind.
assert (HFabs1 : fst (F_241 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 5. unfold snd. unfold F_241. unfold F_231. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_231. unfold fst in HFabs1. unfold F_241 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 238 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (Res := Hind F_244). clear Hind.
assert (HFabs1 : fst (F_244 Nil u1 0 0 0 0)).
apply Res. trivial_in 6. unfold snd. unfold F_244. unfold F_238. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_238. unfold fst in HFabs1. unfold F_244 in HFabs1.    simpl. auto.



	(* REWRITING on [ 241 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_247). clear Hind.
assert (HFabs1 : fst (F_247 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 8. unfold snd. unfold F_247. unfold F_241. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_241. unfold fst in HFabs1. unfold F_247 in HFabs1.   
pattern (C u3 u6), u7. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 244 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (Res := Hind F_250). clear Hind.
assert (HFabs1 : fst (F_250 Nil (C 0 0 ) 0 0 0 0)).
apply Res. trivial_in 7. unfold snd. unfold F_250. unfold F_244. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_244. unfold fst in HFabs1. unfold F_250 in HFabs1.   
pattern (time u1). simpl (le _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 250 ] *)

unfold fst. unfold F_250.
auto.



	(* REWRITING on [ 247 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_253). clear Hind.
assert (HFabs1 : fst (F_253 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 9. unfold snd. unfold F_253. unfold F_247. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_247. unfold fst in HFabs1. unfold F_253 in HFabs1.   
pattern u3, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 253 ] *)

unfold fst. unfold F_253.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_210 := fun f => exists F, In F LF_210 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, f = F e1 e2 e3 e4 e5 e6.

Theorem all_true_210: forall F, In F LF_210 -> forall u1: PLAN, forall u2: OBJ, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, fst (F u1 u2 u3  u4  u5  u6).
Proof.
let n := constr:(6) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_210);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_210;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_210: forall (u2: PLAN) (u1: OBJ), (sortedT (Cons u1 u2)) = true -> (le (timel u2) (time u1)) = true.
Proof.
do 2 intro.
apply (all_true_210 F_210);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_254 :=  PLAN ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_254 : type_LF_254:= (fun   u1  _ _ _ _ => ((sortedT u1) = true -> (progAt u1 (timel u1)) = (erl u1), (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_progAt ((model_PLAN u1):: (Term id_timel ((model_PLAN u1)::nil))::nil))::(Term id_erl ((model_PLAN u1)::nil))::nil)).
Definition F_301 : type_LF_254:= (fun   u6 u2 u3 u4 u5 => (false = true -> (le u2 u3) = false -> (progAt (Cons (C u3 u4) (Cons (C u2 u5) u6)) (timel (Cons (C u3 u4) (Cons (C u2 u5) u6)))) = (erl (Cons (C u3 u4) (Cons (C u2 u5) u6))), (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil)):: (Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::nil))::(Term id_erl ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::nil)).
Definition F_283 : type_LF_254:= (fun    _  _ _ _ _ => (true = true -> (progAt Nil (timel Nil)) = (erl Nil), (Term id_true nil)::(Term id_true nil)::(Term id_progAt ((Term id_Nil nil):: (Term id_timel ((Term id_Nil nil)::nil))::nil))::(Term id_erl ((Term id_Nil nil)::nil))::nil)).
Definition F_289 : type_LF_254:= (fun    _ u3 u4 _ _ => (true = true -> (progAt (Cons (C u3 u4) Nil) (timel (Cons (C u3 u4) Nil))) = (erl (Cons (C u3 u4) Nil)), (Term id_true nil)::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil)):: (Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::nil))::(Term id_erl ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::nil)).
Definition F_295 : type_LF_254:= (fun   u6 u2 u3 u4 u5 => ((sortedT (Cons (C u2 u5) u6)) = true -> (le u2 u3) = true -> (progAt (Cons (C u3 u4) (Cons (C u2 u5) u6)) (timel (Cons (C u3 u4) (Cons (C u2 u5) u6)))) = (erl (Cons (C u3 u4) (Cons (C u2 u5) u6))), (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil)):: (Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::nil))::(Term id_erl ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::nil)).
Definition F_302 : type_LF_254:= (fun    _  _ _ _ _ => ((progAt Nil (timel Nil)) = (erl Nil), (Term id_progAt ((Term id_Nil nil):: (Term id_timel ((Term id_Nil nil)::nil))::nil))::(Term id_erl ((Term id_Nil nil)::nil))::nil)).
Definition F_303 : type_LF_254:= (fun    _ u3 u4 _ _ => ((progAt (Cons (C u3 u4) Nil) (timel (Cons (C u3 u4) Nil))) = (erl (Cons (C u3 u4) Nil)), (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil)):: (Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::nil))::(Term id_erl ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::nil)).
Definition F_306 : type_LF_254:= (fun   u6 u2 u3 u4 u5 => ((sortedT (Cons (C u2 u5) u6)) = true -> (le u2 u3) = true -> (progAt (Cons (C u3 u4) (Cons (C u2 u5) u6)) (timel (Cons (C u3 u4) (Cons (C u2 u5) u6)))) = (er (C u3 u4)), (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil)):: (Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::nil))::(Term id_er ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil))::nil)).
Definition F_309 : type_LF_254:= (fun    _  _ _ _ _ => ((progAt Nil (timel Nil)) = 0, (Term id_progAt ((Term id_Nil nil):: (Term id_timel ((Term id_Nil nil)::nil))::nil))::(Term id_0 nil)::nil)).
Definition F_312 : type_LF_254:= (fun    _ u3 u4 _ _ => ((progAt (Cons (C u3 u4) Nil) (timel (Cons (C u3 u4) Nil))) = (er (C u3 u4)), (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil)):: (Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::nil))::(Term id_er ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil))::nil)).
Definition F_315 : type_LF_254:= (fun   u6 u2 u3 u4 u5 => ((sortedT (Cons (C u2 u5) u6)) = true -> (le u2 u3) = true -> (progAt (Cons (C u3 u4) (Cons (C u2 u5) u6)) (timel (Cons (C u3 u4) (Cons (C u2 u5) u6)))) = u4, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil)):: (Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::nil))::(model_nat u4)::nil)).
Definition F_318 : type_LF_254:= (fun    _  _ _ _ _ => ((progAt Nil 0) = 0, (Term id_progAt ((Term id_Nil nil):: (Term id_0 nil)::nil))::(Term id_0 nil)::nil)).
Definition F_327 : type_LF_254:= (fun    _  _ _ _ _ => (0 = 0, (Term id_0 nil)::(Term id_0 nil)::nil)).
Definition F_321 : type_LF_254:= (fun    _ u3 u4 _ _ => ((progAt (Cons (C u3 u4) Nil) (timel (Cons (C u3 u4) Nil))) = u4, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil)):: (Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil))::nil))::nil))::(model_nat u4)::nil)).
Definition F_324 : type_LF_254:= (fun   u6 u2 u3 u4 u5 => ((sortedT (Cons (C u2 u5) u6)) = true -> (le u2 u3) = true -> (progAt (Cons (C u3 u4) (Cons (C u2 u5) u6)) (time (C u3 u4))) = u4, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil)):: (Term id_time ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil))::nil))::(model_nat u4)::nil)).
Definition F_330 : type_LF_254:= (fun    _ u3 u4 _ _ => ((progAt (Cons (C u3 u4) Nil) (time (C u3 u4))) = u4, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil)):: (Term id_time ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil))::nil))::(model_nat u4)::nil)).
Definition F_334 : type_LF_254:= (fun   u6 u2 u3 u4 u5 => ((sortedT (Cons (C u2 u5) u6)) = true -> (le u2 u3) = true -> (progAt (Cons (C u3 u4) (Cons (C u2 u5) u6)) u3) = u4, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_357 : type_LF_254:= (fun   u6 u2 u3 u4 u5 => ((le u2 u3) = true -> (sortedT u6) = true -> (le (timel u6) (time (C u2 u5))) = true -> (progAt (Cons (C u3 u4) (Cons (C u2 u5) u6)) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (Term id_time ((Term id_C ((model_nat u2):: (model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_337 : type_LF_254:= (fun    _ u3 u4 _ _ => ((progAt (Cons (C u3 u4) Nil) u3) = u4, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_403 : type_LF_254:= (fun    _ u3 u4 _ _ => ((le (time (C u3 u4)) u3) = true -> (er (C u3 u4)) = u4, (Term id_le ((Term id_time ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil))::(model_nat u4)::nil)).
Definition F_407 : type_LF_254:= (fun    _ u3 u4 _ _ => ((le (time (C u3 u4)) u3) = false -> (progAt Nil u3) = u4, (Term id_le ((Term id_time ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Nil nil):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_410 : type_LF_254:= (fun    _ u3 u4 _ _ => ((le u3 u3) = true -> (er (C u3 u4)) = u4, (Term id_le ((model_nat u3):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil))::(model_nat u4)::nil)).
Definition F_417 : type_LF_254:= (fun    _ u3 u4 _ _ => ((le u3 u3) = true -> u4 = u4, (Term id_le ((model_nat u3):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(model_nat u4)::nil)).
Definition F_413 : type_LF_254:= (fun    _ u3 u4 _ _ => ((le (time (C u3 u4)) u3) = false -> 0 = u4, (Term id_le ((Term id_time ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_0 nil)::(model_nat u4)::nil)).
Definition F_420 : type_LF_254:= (fun    _ u3 u4 _ _ => ((le u3 u3) = false -> 0 = u4, (Term id_le ((model_nat u3):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_0 nil)::(model_nat u4)::nil)).
Definition F_361 : type_LF_254:= (fun   u6 u2 u3 u4 u5 => ((le u2 u3) = true -> (sortedT u6) = true -> (le (timel u6) u2) = true -> (progAt (Cons (C u3 u4) (Cons (C u2 u5) u6)) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_450 : type_LF_254:= (fun   u6 u2 u3 u4 _ => ((le u2 u3) = true -> (sortedT u6) = true -> (le (timel u6) u2) = true -> (le (time (C u3 u4)) u3) = true -> (er (C u3 u4)) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil))::(model_nat u4)::nil)).
Definition F_454 : type_LF_254:= (fun   u6 u2 u3 u4 u5 => ((le u2 u3) = true -> (sortedT u6) = true -> (le (timel u6) u2) = true -> (le (time (C u3 u4)) u3) = false -> (progAt (Cons (C u2 u5) u6) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_457 : type_LF_254:= (fun   u6 u2 u3 u4 _ => ((le u2 u3) = true -> (sortedT u6) = true -> (le (timel u6) u2) = true -> (le u3 u3) = true -> (er (C u3 u4)) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u3):: (model_nat u4)::nil))::nil))::(model_nat u4)::nil)).
Definition F_465 : type_LF_254:= (fun   u6 u2 u3 u4 _ => ((le u2 u3) = true -> (sortedT u6) = true -> (le (timel u6) u2) = true -> (le u3 u3) = true -> u4 = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(model_nat u4)::nil)).
Definition F_461 : type_LF_254:= (fun   u6 u2 u3 u4 u5 => ((le u2 u3) = true -> (sortedT u6) = true -> (le (timel u6) u2) = true -> (le u3 u3) = false -> (progAt (Cons (C u2 u5) u6) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u5)::nil)):: (model_PLAN u6)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).

Definition LF_254 := [F_254, F_301, F_283, F_289, F_295, F_302, F_303, F_306, F_309, F_312, F_315, F_318, F_327, F_321, F_324, F_330, F_334, F_357, F_337, F_403, F_407, F_410, F_417, F_413, F_420, F_361, F_450, F_454, F_457, F_465, F_461].


Function f_254 (u1: PLAN) {struct u1} : bool :=
 match u1 with
| Nil => true
| (Cons (C u3 u4) Nil) => true
| (Cons (C u3 u4) (Cons (C u2 u5) u6)) => true
end.

Lemma main_254 : forall F, In F LF_254 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_254 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 254 ] *)

rename u1 into _u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_254 u1). apply f_254_ind.

(* case [ 283 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_283). clear HFabs0.
assert (HFabs0 : fst (F_283 Nil 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_283. unfold F_254. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_254. unfold F_283.
auto.


(* case [ 289 ] *)

intros _u1. intro u3. intro u4.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_289). clear HFabs0.
assert (HFabs0 : fst (F_289 Nil u3 u4 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_289. unfold F_254. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_254. unfold F_289.
auto.



intros _u1. intro u3. intro u4. intro u2. intro u5. intro u6.  intro eq_1.  intro HFabs0.
case_eq (le u2 u3); [intro H | intro H].

(* case [ 295 ] *)

assert (Hind := HFabs0 F_295). clear HFabs0.
assert (HFabs0 : fst (F_295 u6 u2 u3 u4 u5)).
apply Hind. trivial_in 4. unfold snd. unfold F_295. unfold F_254. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_254. unfold F_295. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 301 ] *)

assert (Hind := HFabs0 F_301). clear HFabs0.
assert (HFabs0 : fst (F_301 u6 u2 u3 u4 u5)).
apply Hind. trivial_in 1. unfold snd. unfold F_301. unfold F_254. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_254. unfold F_301. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 301 ] *)

unfold fst. unfold F_301. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 283 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (H := Hind F_302). 
assert (HFabs0 : fst (F_302 Nil 0 0 0 0)).
apply H. trivial_in 5. unfold snd. unfold F_302. unfold F_283. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_283. unfold F_302.

unfold fst in HFabs0. unfold F_302 in HFabs0.
auto.



	(* NEGATIVE DECOMPOSITION on [ 289 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
assert (H := Hind F_303). 
assert (HFabs0 : fst (F_303 Nil u3 u4 0 0)).
apply H. trivial_in 6. unfold snd. unfold F_303. unfold F_289. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_289. unfold F_303.

unfold fst in HFabs0. unfold F_303 in HFabs0.
auto.



	(* REWRITING on [ 295 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_306). clear Hind.
assert (HFabs1 : fst (F_306 u6 u2 u3 u4 u5)).
apply Res. trivial_in 7. unfold snd. unfold F_306. unfold F_295. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_295. unfold fst in HFabs1. unfold F_306 in HFabs1.   
pattern (C u3 u4), (Cons (C u2 u5) u6). simpl (erl _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 302 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (Res := Hind F_309). clear Hind.
assert (HFabs1 : fst (F_309 Nil 0 0 0 0)).
apply Res. trivial_in 8. unfold snd. unfold F_309. unfold F_302. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_302. unfold fst in HFabs1. unfold F_309 in HFabs1.    simpl. auto.



	(* REWRITING on [ 303 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_312). clear Hind.
assert (HFabs1 : fst (F_312 Nil u3 u4 0 0)).
apply Res. trivial_in 9. unfold snd. unfold F_312. unfold F_303. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_303. unfold fst in HFabs1. unfold F_312 in HFabs1.   
pattern (C u3 u4), Nil. simpl (erl _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 306 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_315). clear Hind.
assert (HFabs1 : fst (F_315 u6 u2 u3 u4 u5)).
apply Res. trivial_in 10. unfold snd. unfold F_315. unfold F_306. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_306. unfold fst in HFabs1. unfold F_315 in HFabs1.   
pattern u3, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 309 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (Res := Hind F_318). clear Hind.
assert (HFabs1 : fst (F_318 Nil 0 0 0 0)).
apply Res. trivial_in 11. unfold snd. unfold F_318. unfold F_309. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_309. unfold fst in HFabs1. unfold F_318 in HFabs1.    simpl. auto.



	(* REWRITING on [ 312 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_321). clear Hind.
assert (HFabs1 : fst (F_321 Nil u3 u4 0 0)).
apply Res. trivial_in 13. unfold snd. unfold F_321. unfold F_312. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_312. unfold fst in HFabs1. unfold F_321 in HFabs1.   
pattern u3, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 315 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_324). clear Hind.
assert (HFabs1 : fst (F_324 u6 u2 u3 u4 u5)).
apply Res. trivial_in 14. unfold snd. unfold F_324. unfold F_315. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_315. unfold fst in HFabs1. unfold F_324 in HFabs1.   
pattern (C u3 u4), (Cons (C u2 u5) u6). simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 318 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (Res := Hind F_327). clear Hind.
assert (HFabs1 : fst (F_327 Nil 0 0 0 0)).
apply Res. trivial_in 12. unfold snd. unfold F_327. unfold F_318. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_318. unfold fst in HFabs1. unfold F_327 in HFabs1.   
pattern 0. simpl (progAt _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 327 ] *)

unfold fst. unfold F_327.
auto.



	(* REWRITING on [ 321 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_330). clear Hind.
assert (HFabs1 : fst (F_330 Nil u3 u4 0 0)).
apply Res. trivial_in 15. unfold snd. unfold F_330. unfold F_321. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_321. unfold fst in HFabs1. unfold F_330 in HFabs1.   
pattern (C u3 u4), Nil. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 324 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_334). clear Hind.
assert (HFabs1 : fst (F_334 u6 u2 u3 u4 u5)).
apply Res. trivial_in 16. unfold snd. unfold F_334. unfold F_324. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_324. unfold fst in HFabs1. unfold F_334 in HFabs1.   
pattern u3, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 330 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_337). clear Hind.
assert (HFabs1 : fst (F_337 Nil u3 u4 0 0)).
apply Res. trivial_in 18. unfold snd. unfold F_337. unfold F_330. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_330. unfold fst in HFabs1. unfold F_337 in HFabs1.   
pattern u3, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* AUGMENTATION on [ 334 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. 
assert (H := Hind F_357). clear Hind.
assert (HFabs0: fst (F_357 u6 u2 u3 u4 u5)).
apply H. trivial_in 17. unfold snd. unfold F_334. unfold F_357. rewrite_model. abstract solve_rpo_mul.

unfold fst. unfold F_334.

specialize true_210 with (u1 := (C u2 u5)) (u2 := u6).
specialize true_179 with (u1 := (C u2 u5)) (u2 := u6). auto.




	(* REWRITING on [ 357 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_361). clear Hind.
assert (HFabs1 : fst (F_361 u6 u2 u3 u4 u5)).
apply Res. trivial_in 25. unfold snd. unfold F_361. unfold F_357. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_357. unfold fst in HFabs1. unfold F_361 in HFabs1.   
pattern u2, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 337 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
assert (H: ((le (time (C u3 u4)) u3) = true) \/ ((le (time (C u3 u4)) u3) = false)). 

destruct ((le (time (C u3 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_403). clear Hind.
assert (HFabs0 : fst (F_403 Nil u3 u4 0 0)).
apply H1. trivial_in 19. unfold snd. unfold F_403. unfold F_337. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_337. unfold F_403. unfold fst in HFabs0. unfold F_403 in HFabs0. simpl in HFabs0. 
pattern (C u3 u4).
pattern u3.
pattern Nil.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_407). clear Hind.
assert (HFabs0 : fst (F_407 Nil u3 u4 0 0)).
apply H1. trivial_in 20. unfold snd. unfold F_407. unfold F_337. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_337. unfold F_407. unfold fst in HFabs0. unfold F_407 in HFabs0. simpl in HFabs0. 
pattern (C u3 u4).
pattern u3.
pattern Nil.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 403 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_410). clear Hind.
assert (HFabs1 : fst (F_410 Nil u3 u4 0 0)).
apply Res. trivial_in 21. unfold snd. unfold F_410. unfold F_403. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_403. unfold fst in HFabs1. unfold F_410 in HFabs1.   
pattern u3, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 407 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_413). clear Hind.
assert (HFabs1 : fst (F_413 Nil u3 u4 0 0)).
apply Res. trivial_in 23. unfold snd. unfold F_413. unfold F_407. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_407. unfold fst in HFabs1. unfold F_413 in HFabs1.   
pattern u3. simpl (progAt _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 410 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_417). clear Hind.
assert (HFabs1 : fst (F_417 Nil u3 u4 0 0)).
apply Res. trivial_in 22. unfold snd. unfold F_417. unfold F_410. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_410. unfold fst in HFabs1. unfold F_417 in HFabs1.   
pattern u3, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 417 ] *)

unfold fst. unfold F_417.
auto.



	(* REWRITING on [ 413 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_420). clear Hind.
assert (HFabs1 : fst (F_420 Nil u3 u4 0 0)).
apply Res. trivial_in 24. unfold snd. unfold F_420. unfold F_413. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_413. unfold fst in HFabs1. unfold F_420 in HFabs1.   
pattern u3, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 420 ] *)

rename u1 into d_u1. rename u2 into _u3. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. 
rename _u3 into u3. rename _u4 into u4. 
unfold fst. unfold F_420. specialize true_158 with (u1 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 361 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. 
assert (H: ((le (time (C u3 u4)) u3) = true) \/ ((le (time (C u3 u4)) u3) = false)). 

destruct ((le (time (C u3 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_450). clear Hind.
assert (HFabs0 : fst (F_450 u6 u2 u3 u4 0)).
apply H1. trivial_in 26. unfold snd. unfold F_450. unfold F_361. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_361. unfold F_450. unfold fst in HFabs0. unfold F_450 in HFabs0. simpl in HFabs0. 
pattern (C u3 u4).
pattern u3.
pattern (Cons (C u2 u5) u6).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_454). clear Hind.
assert (HFabs0 : fst (F_454 u6 u2 u3 u4 u5)).
apply H1. trivial_in 27. unfold snd. unfold F_454. unfold F_361. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_361. unfold F_454. unfold fst in HFabs0. unfold F_454 in HFabs0. simpl in HFabs0. 
pattern (C u3 u4).
pattern u3.
pattern (Cons (C u2 u5) u6).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 450 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_457). clear Hind.
assert (HFabs1 : fst (F_457 u6 u2 u3 u4 0)).
apply Res. trivial_in 28. unfold snd. unfold F_457. unfold F_450. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_450. unfold fst in HFabs1. unfold F_457 in HFabs1.   
pattern u3, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 454 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_461). clear Hind.
assert (HFabs1 : fst (F_461 u6 u2 u3 u4 u5)).
apply Res. trivial_in 30. unfold snd. unfold F_461. unfold F_454. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_454. unfold fst in HFabs1. unfold F_461 in HFabs1.   
pattern u3, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 457 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_465). clear Hind.
assert (HFabs1 : fst (F_465 u6 u2 u3 u4 0)).
apply Res. trivial_in 29. unfold snd. unfold F_465. unfold F_457. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_457. unfold fst in HFabs1. unfold F_465 in HFabs1.   
pattern u3, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 465 ] *)

unfold fst. unfold F_465.
auto.



	(* SUBSUMPTION on [ 461 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. 
unfold fst. unfold F_461. specialize true_158 with (u1 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_254 := fun f => exists F, In F LF_254 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_254: forall F, In F LF_254 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2  u3  u4  u5).
Proof.
let n := constr:(5) in
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


Theorem true_254: forall (u1: PLAN), (sortedT u1) = true -> (progAt u1 (timel u1)) = (erl u1).
Proof.
do 1 intro.
apply (all_true_254 F_254);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
