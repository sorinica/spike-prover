
Require Import sorted_insin2_spec.



Definition type_LF_159 :=  nat ->  nat -> (Prop * (List.list term)).

Definition F_159 : type_LF_159:= (fun    u1 u2 => ((le u1 u2) = false -> (le u1 u2) = true -> False, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_174 : type_LF_159:= (fun    u2 _ => (true = false -> (le 0 u2) = true -> False, (Term id_true nil)::(Term id_false nil)::(Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_180 : type_LF_159:= (fun    u3 _ => (false = false -> (le (S u3) 0) = true -> False, (Term id_false nil)::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_186 : type_LF_159:= (fun    u3 u4 => ((le u3 u4) = false -> (le (S u3) (S u4)) = true -> False, (Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_S ((model_nat u4)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_187 : type_LF_159:= (fun    u3 _ => ((le (S u3) 0) = true -> False, (Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_193 : type_LF_159:= (fun     _ _ => (false = true -> False, (Term id_false nil)::(Term id_true nil)::nil)).

Definition LF_159 := [F_159, F_174, F_180, F_186, F_187, F_193].


Function f_159 (u1: nat) (u2: nat) {struct u1} : bool :=
 match u1, u2 with
| 0, _ => true
| (S u3), 0 => true
| (S u3), (S u4) => true
end.

Lemma main_159 : forall F, In F LF_159 -> forall u1, forall u2, (forall F', In F' LF_159 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 159 ] *)

rename u1 into _u1. rename u2 into _u2. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_159 u1 u2). apply f_159_ind.

(* case [ 174 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_174). clear HFabs0.
assert (HFabs0 : fst (F_174 _u2 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_174. unfold F_159. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_159. unfold F_174.
auto.


(* case [ 180 ] *)

intros _u1 _u2. intro u3.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_180). clear HFabs0.
assert (HFabs0 : fst (F_180 u3 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_180. unfold F_159. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_159. unfold F_180.
auto.


(* case [ 186 ] *)

intros _u1 _u2. intro u3.  intro eq_1. intro u4.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_186). clear HFabs0.
assert (HFabs0 : fst (F_186 u3 u4)).
apply Hind. trivial_in 3. unfold snd. unfold F_186. unfold F_159. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_159. unfold F_186.
auto.





	(* NEGATIVE CLASH on [ 174 ] *)

unfold fst. unfold F_174. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 180 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (H := Hind F_187). 
assert (HFabs0 : fst (F_187 u3 0)).
apply H. trivial_in 4. unfold snd. unfold F_187. unfold F_180. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_180. unfold F_187.

unfold fst in HFabs0. unfold F_187 in HFabs0.
auto.



	(* REWRITING on [ 186 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_159). clear Hind.
assert (HFabs1 : fst (F_159 u3 u4)).
apply Res. trivial_in 0. unfold snd. unfold F_159. unfold F_186. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_186. unfold fst in HFabs1. unfold F_159 in HFabs1.   
pattern u3, u4. simpl (le _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 187 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (Res := Hind F_193). clear Hind.
assert (HFabs1 : fst (F_193 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_193. unfold F_187. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_187. unfold fst in HFabs1. unfold F_193 in HFabs1.   
pattern u3. simpl (le _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE CLASH on [ 193 ] *)

unfold fst. unfold F_193. intros. try discriminate.



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


Definition type_LF_197 :=  PLAN ->  OBJ ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_197 : type_LF_197:= (fun  u2 u1  _ _ _ => ((sortedT (Cons u1 u2)) = true -> (sortedT u2) = true, (Term id_sortedT ((Term id_Cons ((model_OBJ u1):: (model_PLAN u2)::nil))::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u2)::nil))::(Term id_true nil)::nil)).
Definition F_217 : type_LF_197:= (fun  u7  _ u3 u4 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (sortedT (Cons (C u3 u6) u7)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_223 : type_LF_197:= (fun  u7  _ u3 u4 u6 => (false = true -> (le u3 u4) = false -> (sortedT (Cons (C u3 u6) u7)) = true, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_211 : type_LF_197:= (fun   _  _  _ _ _ => (true = true -> (sortedT Nil) = true, (Term id_true nil)::(Term id_true nil)::(Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_224 : type_LF_197:= (fun   _  _  _ _ _ => ((sortedT Nil) = true, (Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_227 : type_LF_197:= (fun   _  _  _ _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).

Definition LF_197 := [F_197, F_217, F_223, F_211, F_224, F_227].


Function f_197 (u2: PLAN) (u1: OBJ) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons (C u3 u6) u7), (C u4 u5) => true
end.

Lemma main_197 : forall F, In F LF_197 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_197 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 197 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_197 u2 u1). apply f_197_ind.

(* case [ 211 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_211). clear HFabs0.
assert (HFabs0 : fst (F_211 Nil (C 0 0 ) 0 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_211. unfold F_197. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_197. unfold F_211.
auto.



intros _u2 _u1. intro u3. intro u6. intro u7.  intro eq_1. intro u4. intro u5.  intro eq_2.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 217 ] *)

assert (Hind := HFabs0 F_217). clear HFabs0.
assert (HFabs0 : fst (F_217 u7 (C 0 0 ) u3 u4 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_217. unfold F_197. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_197. unfold F_217. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 223 ] *)

assert (Hind := HFabs0 F_223). clear HFabs0.
assert (HFabs0 : fst (F_223 u7 (C 0 0 ) u3 u4 u6)).
apply Hind. trivial_in 2. unfold snd. unfold F_223. unfold F_197. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_197. unfold F_223. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* TAUTOLOGY on [ 217 ] *)

unfold fst. unfold F_217.
auto.



	(* NEGATIVE CLASH on [ 223 ] *)

unfold fst. unfold F_223. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 211 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (H := Hind F_224). 
assert (HFabs0 : fst (F_224 Nil (C 0 0 ) 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_224. unfold F_211. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_211. unfold F_224.

unfold fst in HFabs0. unfold F_224 in HFabs0.
auto.



	(* REWRITING on [ 224 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (Res := Hind F_227). clear Hind.
assert (HFabs1 : fst (F_227 Nil (C 0 0 ) 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_227. unfold F_224. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_224. unfold fst in HFabs1. unfold F_227 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 227 ] *)

unfold fst. unfold F_227.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_197 := fun f => exists F, In F LF_197 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_197: forall F, In F LF_197 -> forall u1: PLAN, forall u2: OBJ, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2 u3  u4  u5).
Proof.
let n := constr:(5) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_197);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_197;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_197: forall (u2: PLAN) (u1: OBJ), (sortedT (Cons u1 u2)) = true -> (sortedT u2) = true.
Proof.
do 2 intro.
apply (all_true_197 F_197);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_228 :=  PLAN ->  OBJ ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_228 : type_LF_228:= (fun  u2 u1  _ _ _ _ => ((sortedT (Cons u1 u2)) = true -> (le (timel u2) (time u1)) = true, (Term id_sortedT ((Term id_Cons ((model_OBJ u1):: (model_PLAN u2)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u2)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_255 : type_LF_228:= (fun  u7  _ u3 u4 u5 u6 => (false = true -> (le u3 u4) = false -> (le (timel (Cons (C u3 u6) u7)) (time (C u4 u5))) = true, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_243 : type_LF_228:= (fun   _ u1  _ _ _ _ => (true = true -> (le (timel Nil) (time u1)) = true, (Term id_true nil)::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_249 : type_LF_228:= (fun  u7  _ u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (timel (Cons (C u3 u6) u7)) (time (C u4 u5))) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_256 : type_LF_228:= (fun   _ u1  _ _ _ _ => ((le (timel Nil) (time u1)) = true, (Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_259 : type_LF_228:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (timel (Cons (C u3 u6) u7)) u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_262 : type_LF_228:= (fun   _ u1  _ _ _ _ => ((le 0 (time u1)) = true, (Term id_le ((Term id_0 nil):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_268 : type_LF_228:= (fun   _  _  _ _ _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).
Definition F_265 : type_LF_228:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (time (C u3 u6)) u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u3):: (model_nat u6)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_271 : type_LF_228:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le u3 u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::nil)).

Definition LF_228 := [F_228, F_255, F_243, F_249, F_256, F_259, F_262, F_268, F_265, F_271].


Function f_228 (u2: PLAN) (u1: OBJ) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons (C u3 u6) u7), (C u4 u5) => true
end.

Lemma main_228 : forall F, In F LF_228 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, (forall F', In F' LF_228 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, less (snd (F' e1 e2 e3 e4 e5 e6)) (snd (F u1 u2 u3 u4 u5 u6)) -> fst (F' e1 e2 e3 e4 e5 e6)) -> fst (F u1 u2 u3 u4 u5 u6).
Proof.
intros F HF u1 u2 u3 u4 u5 u6; case_In HF; intro Hind.

	(* GENERATE on [ 228 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_228 u2 u1). apply f_228_ind.

(* case [ 243 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_243). clear HFabs0.
assert (HFabs0 : fst (F_243 Nil _u1 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_243. unfold F_228. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_228. unfold F_243.
auto.



intros _u2 _u1. intro u3. intro u6. intro u7.  intro eq_1. intro u4. intro u5.  intro eq_2.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 249 ] *)

assert (Hind := HFabs0 F_249). clear HFabs0.
assert (HFabs0 : fst (F_249 u7 (C 0 0 ) u3 u4 u5 u6)).
apply Hind. trivial_in 3. unfold snd. unfold F_249. unfold F_228. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_228. unfold F_249. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 255 ] *)

assert (Hind := HFabs0 F_255). clear HFabs0.
assert (HFabs0 : fst (F_255 u7 (C 0 0 ) u3 u4 u5 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_255. unfold F_228. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_228. unfold F_255. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 255 ] *)

unfold fst. unfold F_255. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 243 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (H := Hind F_256). 
assert (HFabs0 : fst (F_256 Nil u1 0 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_256. unfold F_243. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_243. unfold F_256.

unfold fst in HFabs0. unfold F_256 in HFabs0.
auto.



	(* REWRITING on [ 249 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_259). clear Hind.
assert (HFabs1 : fst (F_259 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 5. unfold snd. unfold F_259. unfold F_249. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_249. unfold fst in HFabs1. unfold F_259 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 256 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (Res := Hind F_262). clear Hind.
assert (HFabs1 : fst (F_262 Nil u1 0 0 0 0)).
apply Res. trivial_in 6. unfold snd. unfold F_262. unfold F_256. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_256. unfold fst in HFabs1. unfold F_262 in HFabs1.    simpl. auto.



	(* REWRITING on [ 259 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_265). clear Hind.
assert (HFabs1 : fst (F_265 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 8. unfold snd. unfold F_265. unfold F_259. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_259. unfold fst in HFabs1. unfold F_265 in HFabs1.   
pattern (C u3 u6), u7. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 262 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (Res := Hind F_268). clear Hind.
assert (HFabs1 : fst (F_268 Nil (C 0 0 ) 0 0 0 0)).
apply Res. trivial_in 7. unfold snd. unfold F_268. unfold F_262. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_262. unfold fst in HFabs1. unfold F_268 in HFabs1.   
pattern (time u1). simpl (le _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 268 ] *)

unfold fst. unfold F_268.
auto.



	(* REWRITING on [ 265 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_271). clear Hind.
assert (HFabs1 : fst (F_271 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 9. unfold snd. unfold F_271. unfold F_265. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_265. unfold fst in HFabs1. unfold F_271 in HFabs1.   
pattern u3, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 271 ] *)

unfold fst. unfold F_271.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_228 := fun f => exists F, In F LF_228 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, f = F e1 e2 e3 e4 e5 e6.

Theorem all_true_228: forall F, In F LF_228 -> forall u1: PLAN, forall u2: OBJ, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, fst (F u1 u2 u3  u4  u5  u6).
Proof.
let n := constr:(6) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_228);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_228;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_228: forall (u2: PLAN) (u1: OBJ), (sortedT (Cons u1 u2)) = true -> (le (timel u2) (time u1)) = true.
Proof.
do 2 intro.
apply (all_true_228 F_228);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_272 :=  PLAN ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_272 : type_LF_272:= (fun   u1 u2 u3 _ => ((sortedT u1) = true -> (le (timel u1) u2) = true -> (sortedT (Cons (C u2 u3) u1)) = true, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u1)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (model_PLAN u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_288 : type_LF_272:= (fun    _ u2 _ _ => ((sortedT Nil) = true -> (le (timel Nil) u2) = true -> true = true, (Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_true nil)::nil)).
Definition F_294 : type_LF_272:= (fun   u8 u2 u4 u7 => ((sortedT (Cons (C u4 u7) u8)) = true -> (le (timel (Cons (C u4 u7) u8)) u2) = true -> (le u4 u2) = true -> (sortedT (Cons (C u4 u7) u8)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_300 : type_LF_272:= (fun   u8 u2 u4 u7 => ((sortedT (Cons (C u4 u7) u8)) = true -> (le (timel (Cons (C u4 u7) u8)) u2) = true -> (le u4 u2) = false -> false = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_false nil)::(Term id_true nil)::nil)).
Definition F_303 : type_LF_272:= (fun   u8 u2 u4 u7 => ((sortedT (Cons (C u4 u7) u8)) = true -> (le (time (C u4 u7)) u2) = true -> (le u4 u2) = false -> false = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_false nil)::(Term id_true nil)::nil)).
Definition F_306 : type_LF_272:= (fun   u8 u2 u4 u7 => ((sortedT (Cons (C u4 u7) u8)) = true -> (le u4 u2) = true -> (le u4 u2) = false -> false = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u7)::nil)):: (model_PLAN u8)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_false nil)::(Term id_true nil)::nil)).

Definition LF_272 := [F_272, F_288, F_294, F_300, F_303, F_306].


Function f_272 (u1: PLAN) (u2: nat) (u3: nat) {struct u1} : bool :=
 match u1, u2, u3 with
| Nil, _, _ => true
| (Cons (C u4 u7) u8), _, _ => true
end.

Lemma main_272 : forall F, In F LF_272 -> forall u1, forall u2, forall u3, forall u4, (forall F', In F' LF_272 -> forall e1, forall e2, forall e3, forall e4, less (snd (F' e1 e2 e3 e4)) (snd (F u1 u2 u3 u4)) -> fst (F' e1 e2 e3 e4)) -> fst (F u1 u2 u3 u4).
Proof.
intros F HF u1 u2 u3 u4; case_In HF; intro Hind.

	(* GENERATE on [ 272 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. 

revert Hind.

pattern u1, u2, u3, (f_272 u1 u2 u3). apply f_272_ind.

(* case [ 288 ] *)

intros _u1 _u2 _u3.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_288). clear HFabs0.
assert (HFabs0 : fst (F_288 Nil _u2 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_288. unfold F_272. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_272. unfold F_288.
auto.



intros _u1 _u2 _u3. intro u4. intro u7. intro u8.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
case_eq (le u4 _u2); [intro H | intro H].

(* case [ 294 ] *)

assert (Hind := HFabs0 F_294). clear HFabs0.
assert (HFabs0 : fst (F_294 u8 _u2 u4 u7)).
apply Hind. trivial_in 2. unfold snd. unfold F_294. unfold F_272. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_272. unfold F_294. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 300 ] *)

assert (Hind := HFabs0 F_300). clear HFabs0.
assert (HFabs0 : fst (F_300 u8 _u2 u4 u7)).
apply Hind. trivial_in 3. unfold snd. unfold F_300. unfold F_272. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_272. unfold F_300. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* TAUTOLOGY on [ 288 ] *)

unfold fst. unfold F_288.
auto.



	(* TAUTOLOGY on [ 294 ] *)

unfold fst. unfold F_294.
auto.



	(* REWRITING on [ 300 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u4. rename u4 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u4 into u4. rename _u7 into u7. 
assert (Res := Hind F_303). clear Hind.
assert (HFabs1 : fst (F_303 u8 u2 u4 u7)).
apply Res. trivial_in 4. unfold snd. unfold F_303. unfold F_300. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_300. unfold fst in HFabs1. unfold F_303 in HFabs1.   
pattern (C u4 u7), u8. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 303 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u4. rename u4 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u4 into u4. rename _u7 into u7. 
assert (Res := Hind F_306). clear Hind.
assert (HFabs1 : fst (F_306 u8 u2 u4 u7)).
apply Res. trivial_in 5. unfold snd. unfold F_306. unfold F_303. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_303. unfold fst in HFabs1. unfold F_306 in HFabs1.   
pattern u4, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 306 ] *)

rename u1 into _u8. rename u2 into _u2. rename u3 into _u4. rename u4 into _u7. 
rename _u8 into u8. rename _u2 into u2. rename _u4 into u4. rename _u7 into u7. 
unfold fst. unfold F_306. specialize true_159 with (u1 := u4) (u2 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_272 := fun f => exists F, In F LF_272 /\ exists e1, exists e2, exists e3, exists e4, f = F e1 e2 e3 e4.

Theorem all_true_272: forall F, In F LF_272 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, fst (F u1 u2  u3  u4).
Proof.
let n := constr:(4) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_272);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_272;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_272: forall (u1: PLAN) (u2: nat) (u3: nat), (sortedT u1) = true -> (le (timel u1) u2) = true -> (sortedT (Cons (C u2 u3) u1)) = true.
Proof.
do 3 intro.
apply (all_true_272 F_272);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_309 :=  PLAN ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_309 : type_LF_309:= (fun   u1 u2 u3 _ _ => ((sortedT u1) = true -> (le (timel u1) u2) = true -> (sortedT (insIn u1 u2 u3)) = true, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u1)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_insIn ((model_PLAN u1):: (model_nat u2):: (model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_340 : type_LF_309:= (fun    _ u2 u3 _ _ => ((sortedT Nil) = true -> (le (timel Nil) u2) = true -> (sortedT (Cons (C u2 u3) Nil)) = true, (Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_355 : type_LF_309:= (fun    _ u2 _ _ _ => ((sortedT Nil) = true -> (le (timel Nil) u2) = true -> true = true, (Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_true nil)::nil)).
Definition F_346 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((sortedT (Cons (C u8 u9) u6)) = true -> (le (timel (Cons (C u8 u9) u6)) u2) = true -> (le (er (C u8 u9)) u3) = true -> (sortedT (insIn u6 (time (C u8 u9)) u3)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_insIn ((model_PLAN u6):: (Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_352 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((sortedT (Cons (C u8 u9) u6)) = true -> (le (timel (Cons (C u8 u9) u6)) u2) = true -> (le (er (C u8 u9)) u3) = false -> (sortedT (Cons (C u2 u3) (Cons (C u8 u9) u6))) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_358 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((sortedT (Cons (C u8 u9) u6)) = true -> (le (time (C u8 u9)) u2) = true -> (le (er (C u8 u9)) u3) = true -> (sortedT (insIn u6 (time (C u8 u9)) u3)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_insIn ((model_PLAN u6):: (Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_361 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((sortedT (Cons (C u8 u9) u6)) = true -> (le (time (C u8 u9)) u2) = true -> (le (er (C u8 u9)) u3) = false -> (sortedT (Cons (C u2 u3) (Cons (C u8 u9) u6))) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_364 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((sortedT (Cons (C u8 u9) u6)) = true -> (le (time (C u8 u9)) u2) = true -> (le (er (C u8 u9)) u3) = true -> (sortedT (insIn u6 u8 u3)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_insIn ((model_PLAN u6):: (model_nat u8):: (model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_367 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((sortedT (Cons (C u8 u9) u6)) = true -> (le u8 u2) = true -> (le (er (C u8 u9)) u3) = false -> (sortedT (Cons (C u2 u3) (Cons (C u8 u9) u6))) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_370 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((sortedT (Cons (C u8 u9) u6)) = true -> (le u8 u2) = true -> (le (er (C u8 u9)) u3) = true -> (sortedT (insIn u6 u8 u3)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_insIn ((model_PLAN u6):: (model_nat u8):: (model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_373 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((sortedT (Cons (C u8 u9) u6)) = true -> (le u8 u2) = true -> (le u9 u3) = false -> (sortedT (Cons (C u2 u3) (Cons (C u8 u9) u6))) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_398 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((le u8 u2) = true -> (le u9 u3) = false -> (sortedT u6) = true -> (le (timel u6) (time (C u8 u9))) = true -> (sortedT (Cons (C u2 u3) (Cons (C u8 u9) u6))) = true, (Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_376 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((sortedT (Cons (C u8 u9) u6)) = true -> (le u8 u2) = true -> (le u9 u3) = true -> (sortedT (insIn u6 u8 u3)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_insIn ((model_PLAN u6):: (model_nat u8):: (model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_423 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((le u8 u2) = true -> (le u9 u3) = true -> (sortedT u6) = true -> (le (timel u6) (time (C u8 u9))) = true -> (sortedT (insIn u6 u8 u3)) = true, (Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_insIn ((model_PLAN u6):: (model_nat u8):: (model_nat u3)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_401 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((le u8 u2) = true -> (le u9 u3) = false -> (sortedT u6) = true -> (le (timel u6) u8) = true -> (sortedT (Cons (C u2 u3) (Cons (C u8 u9) u6))) = true, (Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (model_nat u8)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_479 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((le u8 u2) = true -> (le u9 u3) = false -> (sortedT u6) = true -> (le (timel u6) u8) = true -> (le u8 u2) = true -> (sortedT (Cons (C u8 u9) u6)) = true, (Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (model_nat u8)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_483 : type_LF_309:= (fun   u6 u2 u3 u8 u9 => ((le u8 u2) = true -> (le u9 u3) = false -> (sortedT u6) = true -> (le (timel u6) u8) = true -> (le u8 u2) = false -> false = true, (Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u9):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_sortedT ((model_PLAN u6)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u6)::nil)):: (model_nat u8)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_false nil)::(Term id_true nil)::nil)).

Definition LF_309 := [F_309, F_340, F_355, F_346, F_352, F_358, F_361, F_364, F_367, F_370, F_373, F_398, F_376, F_423, F_401, F_479, F_483].


Function f_309 (u1: PLAN) (u2: nat) (u3: nat) {struct u1} : PLAN :=
 match u1, u2, u3 with
| Nil, _, _ => Nil
| (Cons (C u8 u9) u6), _, _ => Nil
end.

Lemma main_309 : forall F, In F LF_309 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_309 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 309 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. 

revert Hind.

pattern u1, u2, u3, (f_309 u1 u2 u3). apply f_309_ind.

(* case [ 340 ] *)

intros _u1 _u2 _u3.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_340). clear HFabs0.
assert (HFabs0 : fst (F_340 Nil _u2 _u3 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_340. unfold F_309. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_309. unfold F_340.
auto.



intros _u1 _u2 _u3. intro u8. intro u9. intro u6.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
case_eq (le (er (C u8 u9)) _u3); [intro H | intro H].

(* case [ 346 ] *)

assert (Hind := HFabs0 F_346). clear HFabs0.
assert (HFabs0 : fst (F_346 u6 _u2 _u3 u8 u9)).
apply Hind. trivial_in 3. unfold snd. unfold F_346. unfold F_309. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_309. unfold F_346. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 352 ] *)

assert (Hind := HFabs0 F_352). clear HFabs0.
assert (HFabs0 : fst (F_352 u6 _u2 _u3 u8 u9)).
apply Hind. trivial_in 4. unfold snd. unfold F_352. unfold F_309. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_309. unfold F_352. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* REWRITING on [ 340 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_355). clear Hind.
assert (HFabs1 : fst (F_355 Nil u2 0 0 0)).
apply Res. trivial_in 2. unfold snd. unfold F_355. unfold F_340. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_340. unfold fst in HFabs1. unfold F_355 in HFabs1.   
pattern (C u2 u3). simpl (sortedT _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 355 ] *)

unfold fst. unfold F_355.
auto.



	(* REWRITING on [ 346 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_358). clear Hind.
assert (HFabs1 : fst (F_358 u6 u2 u3 u8 u9)).
apply Res. trivial_in 5. unfold snd. unfold F_358. unfold F_346. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_346. unfold fst in HFabs1. unfold F_358 in HFabs1.   
pattern (C u8 u9), u6. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 352 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_361). clear Hind.
assert (HFabs1 : fst (F_361 u6 u2 u3 u8 u9)).
apply Res. trivial_in 6. unfold snd. unfold F_361. unfold F_352. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_352. unfold fst in HFabs1. unfold F_361 in HFabs1.   
pattern (C u8 u9), u6. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 358 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_364). clear Hind.
assert (HFabs1 : fst (F_364 u6 u2 u3 u8 u9)).
apply Res. trivial_in 7. unfold snd. unfold F_364. unfold F_358. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_358. unfold fst in HFabs1. unfold F_364 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 361 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_367). clear Hind.
assert (HFabs1 : fst (F_367 u6 u2 u3 u8 u9)).
apply Res. trivial_in 8. unfold snd. unfold F_367. unfold F_361. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_361. unfold fst in HFabs1. unfold F_367 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 364 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_370). clear Hind.
assert (HFabs1 : fst (F_370 u6 u2 u3 u8 u9)).
apply Res. trivial_in 9. unfold snd. unfold F_370. unfold F_364. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_364. unfold fst in HFabs1. unfold F_370 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 367 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_373). clear Hind.
assert (HFabs1 : fst (F_373 u6 u2 u3 u8 u9)).
apply Res. trivial_in 10. unfold snd. unfold F_373. unfold F_367. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_367. unfold fst in HFabs1. unfold F_373 in HFabs1.   
pattern u8, u9. simpl (er _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 370 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_376). clear Hind.
assert (HFabs1 : fst (F_376 u6 u2 u3 u8 u9)).
apply Res. trivial_in 12. unfold snd. unfold F_376. unfold F_370. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_370. unfold fst in HFabs1. unfold F_376 in HFabs1.   
pattern u8, u9. simpl (er _). cbv beta.
 simpl. auto.



	(* AUGMENTATION on [ 373 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (H := Hind F_398). clear Hind.
assert (HFabs0: fst (F_398 u6 u2 u3 u8 u9)).
apply H. trivial_in 11. unfold snd. unfold F_373. unfold F_398. rewrite_model. abstract solve_rpo_mul.

unfold fst. unfold F_373.

specialize true_228 with (u1 := (C u8 u9)) (u2 := u6).
specialize true_197 with (u1 := (C u8 u9)) (u2 := u6). auto.




	(* REWRITING on [ 398 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_401). clear Hind.
assert (HFabs1 : fst (F_401 u6 u2 u3 u8 u9)).
apply Res. trivial_in 14. unfold snd. unfold F_401. unfold F_398. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_398. unfold fst in HFabs1. unfold F_401 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* AUGMENTATION on [ 376 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (H := Hind F_423). clear Hind.
assert (HFabs0: fst (F_423 u6 u2 u3 u8 u9)).
apply H. trivial_in 13. unfold snd. unfold F_376. unfold F_423. rewrite_model. abstract solve_rpo_mul.

unfold fst. unfold F_376.

specialize true_228 with (u1 := (C u8 u9)) (u2 := u6).
specialize true_197 with (u1 := (C u8 u9)) (u2 := u6). auto.




	(* REWRITING on [ 423 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_309). clear Hind.
assert (HFabs1 : fst (F_309 u6 u8 u3 0 0)).
apply Res. trivial_in 0. unfold snd. unfold F_309. unfold F_423. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_423. unfold fst in HFabs1. unfold F_309 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 401 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (H: ((le u8 u2) = true) \/ ((le u8 u2) = false)). 

destruct ((le u8 u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 109 ] *)

assert (H1 := Hind F_479). clear Hind.
assert (HFabs0 : fst (F_479 u6 u2 u3 u8 u9)).
apply H1. trivial_in 15. unfold snd. unfold F_479. unfold F_401. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_401. unfold F_479. unfold fst in HFabs0. unfold F_479 in HFabs0. simpl in HFabs0. 
pattern u8.
pattern u2.
pattern u3.
pattern u9.
pattern u6.
simpl (sortedT _). cbv beta. try unfold sortedT. try rewrite H. try rewrite H0. try unfold sortedT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 110 ] *)

assert (H1 := Hind F_483). clear Hind.
assert (HFabs0 : fst (F_483 u6 u2 u3 u8 u9)).
apply H1. trivial_in 16. unfold snd. unfold F_483. unfold F_401. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_401. unfold F_483. unfold fst in HFabs0. unfold F_483 in HFabs0. simpl in HFabs0. 
pattern u8.
pattern u2.
pattern u3.
pattern u9.
pattern u6.
simpl (sortedT _). cbv beta. try unfold sortedT. try rewrite H. try rewrite H0. try unfold sortedT in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* SUBSUMPTION on [ 479 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
unfold fst. unfold F_479. specialize true_272 with (u1 := u6) (u2 := u8) (u3 := u9).
(auto || symmetry; auto).



	(* SUBSUMPTION on [ 483 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
unfold fst. unfold F_483. specialize true_159 with (u1 := u8) (u2 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_309 := fun f => exists F, In F LF_309 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_309: forall F, In F LF_309 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2  u3  u4  u5).
Proof.
let n := constr:(5) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_309);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_309;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_309: forall (u1: PLAN) (u2: nat) (u3: nat), (sortedT u1) = true -> (le (timel u1) u2) = true -> (sortedT (insIn u1 u2 u3)) = true.
Proof.
do 3 intro.
apply (all_true_309 F_309);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
