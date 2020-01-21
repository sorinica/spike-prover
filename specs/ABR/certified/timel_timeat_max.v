
Require Import timel_timeat_max_spec.



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


Definition type_LF_196 :=  PLAN ->  OBJ ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_196 : type_LF_196:= (fun  u2 u1  _ _ _ => ((sortedT (Cons u1 u2)) = true -> (sortedT u2) = true, (Term id_sortedT ((Term id_Cons ((model_OBJ u1):: (model_PLAN u2)::nil))::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u2)::nil))::(Term id_true nil)::nil)).
Definition F_216 : type_LF_196:= (fun  u7  _ u3 u4 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (sortedT (Cons (C u3 u6) u7)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_222 : type_LF_196:= (fun  u7  _ u3 u4 u6 => (false = true -> (le u3 u4) = false -> (sortedT (Cons (C u3 u6) u7)) = true, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_210 : type_LF_196:= (fun   _  _  _ _ _ => (true = true -> (sortedT Nil) = true, (Term id_true nil)::(Term id_true nil)::(Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_223 : type_LF_196:= (fun   _  _  _ _ _ => ((sortedT Nil) = true, (Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_226 : type_LF_196:= (fun   _  _  _ _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).

Definition LF_196 := [F_196, F_216, F_222, F_210, F_223, F_226].


Function f_196 (u2: PLAN) (u1: OBJ) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons (C u3 u6) u7), (C u4 u5) => true
end.

Lemma main_196 : forall F, In F LF_196 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_196 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 196 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_196 u2 u1). apply f_196_ind.

(* case [ 210 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_210). clear HFabs0.
assert (HFabs0 : fst (F_210 Nil (C 0 0 ) 0 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_210. unfold F_196. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_196. unfold F_210.
auto.



intros _u2 _u1. intro u3. intro u6. intro u7.  intro eq_1. intro u4. intro u5.  intro eq_2.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 216 ] *)

assert (Hind := HFabs0 F_216). clear HFabs0.
assert (HFabs0 : fst (F_216 u7 (C 0 0 ) u3 u4 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_216. unfold F_196. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_196. unfold F_216. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 222 ] *)

assert (Hind := HFabs0 F_222). clear HFabs0.
assert (HFabs0 : fst (F_222 u7 (C 0 0 ) u3 u4 u6)).
apply Hind. trivial_in 2. unfold snd. unfold F_222. unfold F_196. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_196. unfold F_222. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* TAUTOLOGY on [ 216 ] *)

unfold fst. unfold F_216.
auto.



	(* NEGATIVE CLASH on [ 222 ] *)

unfold fst. unfold F_222. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 210 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (H := Hind F_223). 
assert (HFabs0 : fst (F_223 Nil (C 0 0 ) 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_223. unfold F_210. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_210. unfold F_223.

unfold fst in HFabs0. unfold F_223 in HFabs0.
auto.



	(* REWRITING on [ 223 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (Res := Hind F_226). clear Hind.
assert (HFabs1 : fst (F_226 Nil (C 0 0 ) 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_226. unfold F_223. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_223. unfold fst in HFabs1. unfold F_226 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 226 ] *)

unfold fst. unfold F_226.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_196 := fun f => exists F, In F LF_196 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_196: forall F, In F LF_196 -> forall u1: PLAN, forall u2: OBJ, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2 u3  u4  u5).
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


Theorem true_196: forall (u2: PLAN) (u1: OBJ), (sortedT (Cons u1 u2)) = true -> (sortedT u2) = true.
Proof.
do 2 intro.
apply (all_true_196 F_196);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_227 :=  PLAN ->  nat ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_227 : type_LF_227:= (fun   u1 u2 _ _ _ _ => ((sortedT u1) = true -> (le (timel u1) u2) = true -> (timeAt u1 u2) = (timel u1), (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u1)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timeAt ((model_PLAN u1):: (model_nat u2)::nil))::(Term id_timel ((model_PLAN u1)::nil))::nil)).
Definition F_274 : type_LF_227:= (fun   u7 u2 u3 u4 u5 u6 => (false = true -> (le (timel (Cons (C u4 u5) (Cons (C u3 u6) u7))) u2) = true -> (le u3 u4) = false -> (timeAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) = (timel (Cons (C u4 u5) (Cons (C u3 u6) u7))), (Term id_false nil)::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil))::nil)).
Definition F_256 : type_LF_227:= (fun    _ u2 _ _ _ _ => (true = true -> (le (timel Nil) u2) = true -> (timeAt Nil u2) = (timel Nil), (Term id_true nil)::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_timel ((Term id_Nil nil)::nil))::nil)).
Definition F_262 : type_LF_227:= (fun    _ u2 u4 u5 _ _ => (true = true -> (le (timel (Cons (C u4 u5) Nil)) u2) = true -> (timeAt (Cons (C u4 u5) Nil) u2) = (timel (Cons (C u4 u5) Nil)), (Term id_true nil)::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil))::nil)).
Definition F_268 : type_LF_227:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le (timel (Cons (C u4 u5) (Cons (C u3 u6) u7))) u2) = true -> (le u3 u4) = true -> (timeAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) = (timel (Cons (C u4 u5) (Cons (C u3 u6) u7))), (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil))::nil)).
Definition F_275 : type_LF_227:= (fun    _ u2 _ _ _ _ => ((le (timel Nil) u2) = true -> (timeAt Nil u2) = (timel Nil), (Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_timel ((Term id_Nil nil)::nil))::nil)).
Definition F_276 : type_LF_227:= (fun    _ u2 u4 u5 _ _ => ((le (timel (Cons (C u4 u5) Nil)) u2) = true -> (timeAt (Cons (C u4 u5) Nil) u2) = (timel (Cons (C u4 u5) Nil)), (Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil))::nil)).
Definition F_279 : type_LF_227:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le (timel (Cons (C u4 u5) (Cons (C u3 u6) u7))) u2) = true -> (le u3 u4) = true -> (timeAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) = (time (C u4 u5)), (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil)).
Definition F_282 : type_LF_227:= (fun    _ u2 _ _ _ _ => ((le (timel Nil) u2) = true -> (timeAt Nil u2) = 0, (Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_0 nil)::nil)).
Definition F_285 : type_LF_227:= (fun    _ u2 u4 u5 _ _ => ((le (timel (Cons (C u4 u5) Nil)) u2) = true -> (timeAt (Cons (C u4 u5) Nil) u2) = (time (C u4 u5)), (Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil)).
Definition F_288 : type_LF_227:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le (time (C u4 u5)) u2) = true -> (le u3 u4) = true -> (timeAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) = (time (C u4 u5)), (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil)).
Definition F_291 : type_LF_227:= (fun    _ u2 _ _ _ _ => ((le 0 u2) = true -> (timeAt Nil u2) = 0, (Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_0 nil)::nil)).
Definition F_300 : type_LF_227:= (fun    _ u2 _ _ _ _ => ((le 0 u2) = true -> 0 = 0, (Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_0 nil)::(Term id_0 nil)::nil)).
Definition F_294 : type_LF_227:= (fun    _ u2 u4 u5 _ _ => ((le (time (C u4 u5)) u2) = true -> (timeAt (Cons (C u4 u5) Nil) u2) = (time (C u4 u5)), (Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil)).
Definition F_297 : type_LF_227:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le (time (C u4 u5)) u2) = true -> (le u3 u4) = true -> (timeAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) = u4, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil))::(model_nat u4)::nil)).
Definition F_303 : type_LF_227:= (fun    _ u2 u4 u5 _ _ => ((le (time (C u4 u5)) u2) = true -> (timeAt (Cons (C u4 u5) Nil) u2) = u4, (Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(model_nat u4)::nil)).
Definition F_306 : type_LF_227:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u4 u2) = true -> (le u3 u4) = true -> (timeAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) = u4, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil))::(model_nat u4)::nil)).
Definition F_328 : type_LF_227:= (fun   u7 u2 u3 u4 u5 u6 => ((le u4 u2) = true -> (le u3 u4) = true -> (sortedT u7) = true -> (le (timel u7) (time (C u3 u6))) = true -> (timeAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) = u4, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u7)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u7)::nil)):: (Term id_time ((Term id_C ((model_nat u3):: (model_nat u6)::nil))::nil))::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil))::(model_nat u4)::nil)).
Definition F_309 : type_LF_227:= (fun    _ u2 u4 u5 _ _ => ((le u4 u2) = true -> (timeAt (Cons (C u4 u5) Nil) u2) = u4, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(model_nat u4)::nil)).
Definition F_371 : type_LF_227:= (fun    _ u2 u4 u5 _ _ => ((le u4 u2) = true -> (le (time (C u4 u5)) u2) = true -> (time (C u4 u5)) = u4, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::(model_nat u4)::nil)).
Definition F_378 : type_LF_227:= (fun    _ u2 u4 u5 _ _ => ((le u4 u2) = true -> (le (time (C u4 u5)) u2) = true -> u4 = u4, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(model_nat u4)::(model_nat u4)::nil)).
Definition F_375 : type_LF_227:= (fun    _ u2 u4 u5 _ _ => ((le u4 u2) = true -> (le (time (C u4 u5)) u2) = false -> (timeAt Nil u2) = u4, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_timeAt ((Term id_Nil nil):: (model_nat u2)::nil))::(model_nat u4)::nil)).
Definition F_381 : type_LF_227:= (fun    _ u2 u4 u5 _ _ => ((le u4 u2) = true -> (le (time (C u4 u5)) u2) = false -> 0 = u4, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_0 nil)::(model_nat u4)::nil)).
Definition F_384 : type_LF_227:= (fun    _ u2 u4 _ _ _ => ((le u4 u2) = true -> (le u4 u2) = false -> 0 = u4, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_0 nil)::(model_nat u4)::nil)).
Definition F_331 : type_LF_227:= (fun   u7 u2 u3 u4 u5 u6 => ((le u4 u2) = true -> (le u3 u4) = true -> (sortedT u7) = true -> (le (timel u7) u3) = true -> (timeAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) = u4, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u7)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u7)::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil))::(model_nat u4)::nil)).
Definition F_413 : type_LF_227:= (fun   u7 u2 u3 u4 u5 _ => ((le u4 u2) = true -> (le u3 u4) = true -> (sortedT u7) = true -> (le (timel u7) u3) = true -> (le (time (C u4 u5)) u2) = true -> (time (C u4 u5)) = u4, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u7)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u7)::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::(model_nat u4)::nil)).
Definition F_420 : type_LF_227:= (fun   u7 u2 u3 u4 u5 _ => ((le u4 u2) = true -> (le u3 u4) = true -> (sortedT u7) = true -> (le (timel u7) u3) = true -> (le (time (C u4 u5)) u2) = true -> u4 = u4, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u7)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u7)::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(model_nat u4)::(model_nat u4)::nil)).
Definition F_417 : type_LF_227:= (fun   u7 u2 u3 u4 u5 u6 => ((le u4 u2) = true -> (le u3 u4) = true -> (sortedT u7) = true -> (le (timel u7) u3) = true -> (le (time (C u4 u5)) u2) = false -> (timeAt (Cons (C u3 u6) u7) u2) = u4, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u7)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u7)::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u4)::nil)).
Definition F_423 : type_LF_227:= (fun   u7 u2 u3 u4 u6 _ => ((le u4 u2) = true -> (le u3 u4) = true -> (sortedT u7) = true -> (le (timel u7) u3) = true -> (le u4 u2) = false -> (timeAt (Cons (C u3 u6) u7) u2) = u4, (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u7)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u7)::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_timeAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u4)::nil)).

Definition LF_227 := [F_227, F_274, F_256, F_262, F_268, F_275, F_276, F_279, F_282, F_285, F_288, F_291, F_300, F_294, F_297, F_303, F_306, F_328, F_309, F_371, F_378, F_375, F_381, F_384, F_331, F_413, F_420, F_417, F_423].


Function f_227 (u1: PLAN) {struct u1} : bool :=
 match u1 with
| Nil => true
| (Cons (C u4 u5) Nil) => true
| (Cons (C u4 u5) (Cons (C u3 u6) u7)) => true
end.


Hypothesis true_156: forall u1 u2, (sortedT (Cons u1 u2)) = true -> (le (timel u2) (time u1)) = true.

Lemma main_227 : forall F, In F LF_227 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, (forall F', In F' LF_227 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, less (snd (F' e1 e2 e3 e4 e5 e6)) (snd (F u1 u2 u3 u4 u5 u6)) -> fst (F' e1 e2 e3 e4 e5 e6)) -> fst (F u1 u2 u3 u4 u5 u6).
Proof.
intros F HF u1 u2 u3 u4 u5 u6; case_In HF; intro Hind.

	(* GENERATE on [ 227 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, (f_227 u1). apply f_227_ind.

(* case [ 256 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_256). clear HFabs0.
assert (HFabs0 : fst (F_256 Nil u2 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_256. unfold F_227. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_227. unfold F_256.
auto.


(* case [ 262 ] *)

intros _u1. intro u4. intro u5.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_262). clear HFabs0.
assert (HFabs0 : fst (F_262 Nil u2 u4 u5 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_262. unfold F_227. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_227. unfold F_262.
auto.



intros _u1. intro u4. intro u5. intro u3. intro u6. intro u7.  intro eq_1.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 268 ] *)

assert (Hind := HFabs0 F_268). clear HFabs0.
assert (HFabs0 : fst (F_268 u7 u2 u3 u4 u5 u6)).
apply Hind. trivial_in 4. unfold snd. unfold F_268. unfold F_227. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_227. unfold F_268. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 274 ] *)

assert (Hind := HFabs0 F_274). clear HFabs0.
assert (HFabs0 : fst (F_274 u7 u2 u3 u4 u5 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_274. unfold F_227. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_227. unfold F_274. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 274 ] *)

unfold fst. unfold F_274. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 256 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. 
assert (H := Hind F_275). 
assert (HFabs0 : fst (F_275 Nil u2 0 0 0 0)).
apply H. trivial_in 5. unfold snd. unfold F_275. unfold F_256. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_256. unfold F_275.

unfold fst in HFabs0. unfold F_275 in HFabs0.
auto.



	(* NEGATIVE DECOMPOSITION on [ 262 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (H := Hind F_276). 
assert (HFabs0 : fst (F_276 Nil u2 u4 u5 0 0)).
apply H. trivial_in 6. unfold snd. unfold F_276. unfold F_262. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_262. unfold F_276.

unfold fst in HFabs0. unfold F_276 in HFabs0.
auto.



	(* REWRITING on [ 268 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_279). clear Hind.
assert (HFabs1 : fst (F_279 u7 u2 u3 u4 u5 u6)).
apply Res. trivial_in 7. unfold snd. unfold F_279. unfold F_268. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_268. unfold fst in HFabs1. unfold F_279 in HFabs1.   
pattern (C u4 u5), (Cons (C u3 u6) u7). simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 275 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. 
assert (Res := Hind F_282). clear Hind.
assert (HFabs1 : fst (F_282 Nil u2 0 0 0 0)).
apply Res. trivial_in 8. unfold snd. unfold F_282. unfold F_275. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_275. unfold fst in HFabs1. unfold F_282 in HFabs1.    simpl. auto.



	(* REWRITING on [ 276 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_285). clear Hind.
assert (HFabs1 : fst (F_285 Nil u2 u4 u5 0 0)).
apply Res. trivial_in 9. unfold snd. unfold F_285. unfold F_276. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_276. unfold fst in HFabs1. unfold F_285 in HFabs1.   
pattern (C u4 u5), Nil. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 279 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_288). clear Hind.
assert (HFabs1 : fst (F_288 u7 u2 u3 u4 u5 u6)).
apply Res. trivial_in 10. unfold snd. unfold F_288. unfold F_279. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_279. unfold fst in HFabs1. unfold F_288 in HFabs1.   
pattern (C u4 u5), (Cons (C u3 u6) u7). simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 282 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. 
assert (Res := Hind F_291). clear Hind.
assert (HFabs1 : fst (F_291 Nil u2 0 0 0 0)).
apply Res. trivial_in 11. unfold snd. unfold F_291. unfold F_282. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_282. unfold fst in HFabs1. unfold F_291 in HFabs1.    simpl. auto.



	(* REWRITING on [ 285 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_294). clear Hind.
assert (HFabs1 : fst (F_294 Nil u2 u4 u5 0 0)).
apply Res. trivial_in 13. unfold snd. unfold F_294. unfold F_285. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_285. unfold fst in HFabs1. unfold F_294 in HFabs1.   
pattern (C u4 u5), Nil. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 288 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_297). clear Hind.
assert (HFabs1 : fst (F_297 u7 u2 u3 u4 u5 u6)).
apply Res. trivial_in 14. unfold snd. unfold F_297. unfold F_288. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_288. unfold fst in HFabs1. unfold F_297 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 291 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. 
assert (Res := Hind F_300). clear Hind.
assert (HFabs1 : fst (F_300 Nil u2 0 0 0 0)).
apply Res. trivial_in 12. unfold snd. unfold F_300. unfold F_291. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_291. unfold fst in HFabs1. unfold F_300 in HFabs1.   
pattern u2. simpl (timeAt _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 300 ] *)

unfold fst. unfold F_300.
auto.



	(* REWRITING on [ 294 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_303). clear Hind.
assert (HFabs1 : fst (F_303 Nil u2 u4 u5 0 0)).
apply Res. trivial_in 15. unfold snd. unfold F_303. unfold F_294. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_294. unfold fst in HFabs1. unfold F_303 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 297 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_306). clear Hind.
assert (HFabs1 : fst (F_306 u7 u2 u3 u4 u5 u6)).
apply Res. trivial_in 16. unfold snd. unfold F_306. unfold F_297. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_297. unfold fst in HFabs1. unfold F_306 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 303 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_309). clear Hind.
assert (HFabs1 : fst (F_309 Nil u2 u4 u5 0 0)).
apply Res. trivial_in 18. unfold snd. unfold F_309. unfold F_303. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_303. unfold fst in HFabs1. unfold F_309 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* AUGMENTATION on [ 306 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (H := Hind F_328). clear Hind.
assert (HFabs0: fst (F_328 u7 u2 u3 u4 u5 u6)).
apply H. trivial_in 17. unfold snd. unfold F_306. unfold F_328. rewrite_model. abstract solve_rpo_mul.

unfold fst. unfold F_306.

specialize true_156 with (u1 := (C u3 u6)) (u2 := u7).
specialize true_196 with (u1 := (C u3 u6)) (u2 := u7). auto.




	(* REWRITING on [ 328 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_331). clear Hind.
assert (HFabs1 : fst (F_331 u7 u2 u3 u4 u5 u6)).
apply Res. trivial_in 24. unfold snd. unfold F_331. unfold F_328. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_328. unfold fst in HFabs1. unfold F_331 in HFabs1.   
pattern u3, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 309 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (H: ((le (time (C u4 u5)) u2) = true) \/ ((le (time (C u4 u5)) u2) = false)). 

destruct ((le (time (C u4 u5)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 140 ] *)

assert (H1 := Hind F_371). clear Hind.
assert (HFabs0 : fst (F_371 Nil u2 u4 u5 0 0)).
apply H1. trivial_in 19. unfold snd. unfold F_371. unfold F_309. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_309. unfold F_371. unfold fst in HFabs0. unfold F_371 in HFabs0. simpl in HFabs0. 
pattern (C u4 u5).
pattern u2.
pattern Nil.
simpl (timeAt _ _). cbv beta. try unfold timeAt. try rewrite H. try rewrite H0. try unfold timeAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 141 ] *)

assert (H1 := Hind F_375). clear Hind.
assert (HFabs0 : fst (F_375 Nil u2 u4 u5 0 0)).
apply H1. trivial_in 21. unfold snd. unfold F_375. unfold F_309. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_309. unfold F_375. unfold fst in HFabs0. unfold F_375 in HFabs0. simpl in HFabs0. 
pattern (C u4 u5).
pattern u2.
pattern Nil.
simpl (timeAt _ _). cbv beta. try unfold timeAt. try rewrite H. try rewrite H0. try unfold timeAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 371 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_378). clear Hind.
assert (HFabs1 : fst (F_378 Nil u2 u4 u5 0 0)).
apply Res. trivial_in 20. unfold snd. unfold F_378. unfold F_371. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_371. unfold fst in HFabs1. unfold F_378 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 378 ] *)

unfold fst. unfold F_378.
auto.



	(* REWRITING on [ 375 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_381). clear Hind.
assert (HFabs1 : fst (F_381 Nil u2 u4 u5 0 0)).
apply Res. trivial_in 22. unfold snd. unfold F_381. unfold F_375. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_375. unfold fst in HFabs1. unfold F_381 in HFabs1.   
pattern u2. simpl (timeAt _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 381 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_384). clear Hind.
assert (HFabs1 : fst (F_384 Nil u2 u4 0 0 0)).
apply Res. trivial_in 23. unfold snd. unfold F_384. unfold F_381. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_381. unfold fst in HFabs1. unfold F_384 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 384 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. 
unfold fst. unfold F_384. specialize true_158 with (u1 := u4) (u2 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 331 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (H: ((le (time (C u4 u5)) u2) = true) \/ ((le (time (C u4 u5)) u2) = false)). 

destruct ((le (time (C u4 u5)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 140 ] *)

assert (H1 := Hind F_413). clear Hind.
assert (HFabs0 : fst (F_413 u7 u2 u3 u4 u5 0)).
apply H1. trivial_in 25. unfold snd. unfold F_413. unfold F_331. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_331. unfold F_413. unfold fst in HFabs0. unfold F_413 in HFabs0. simpl in HFabs0. 
pattern (C u4 u5).
pattern u2.
pattern (Cons (C u3 u6) u7).
simpl (timeAt _ _). cbv beta. try unfold timeAt. try rewrite H. try rewrite H0. try unfold timeAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 141 ] *)

assert (H1 := Hind F_417). clear Hind.
assert (HFabs0 : fst (F_417 u7 u2 u3 u4 u5 u6)).
apply H1. trivial_in 27. unfold snd. unfold F_417. unfold F_331. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_331. unfold F_417. unfold fst in HFabs0. unfold F_417 in HFabs0. simpl in HFabs0. 
pattern (C u4 u5).
pattern u2.
pattern (Cons (C u3 u6) u7).
simpl (timeAt _ _). cbv beta. try unfold timeAt. try rewrite H. try rewrite H0. try unfold timeAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 413 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into d_u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_420). clear Hind.
assert (HFabs1 : fst (F_420 u7 u2 u3 u4 u5 0)).
apply Res. trivial_in 26. unfold snd. unfold F_420. unfold F_413. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_413. unfold fst in HFabs1. unfold F_420 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 420 ] *)

unfold fst. unfold F_420.
auto.



	(* REWRITING on [ 417 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_423). clear Hind.
assert (HFabs1 : fst (F_423 u7 u2 u3 u4 u6 0)).
apply Res. trivial_in 28. unfold snd. unfold F_423. unfold F_417. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_417. unfold fst in HFabs1. unfold F_423 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 423 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
unfold fst. unfold F_423. specialize true_158 with (u1 := u4) (u2 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_227 := fun f => exists F, In F LF_227 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, f = F e1 e2 e3 e4 e5 e6.

Theorem all_true_227: forall F, In F LF_227 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, fst (F u1 u2  u3  u4  u5  u6).
Proof.
let n := constr:(6) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_227);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_227;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_227: forall (u1: PLAN) (u2: nat), (sortedT u1) = true -> (le (timel u1) u2) = true -> (timeAt u1 u2) = (timel u1).
Proof.
do 2 intro.
apply (all_true_227 F_227);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
