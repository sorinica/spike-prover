
Require Import progat_insat1_spec.



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


Definition type_LF_227 :=  PLAN ->  OBJ ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_227 : type_LF_227:= (fun  u2 u1  _ _ _ _ => ((sortedT (Cons u1 u2)) = true -> (le (timel u2) (time u1)) = true, (Term id_sortedT ((Term id_Cons ((model_OBJ u1):: (model_PLAN u2)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u2)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_254 : type_LF_227:= (fun  u7  _ u3 u4 u5 u6 => (false = true -> (le u3 u4) = false -> (le (timel (Cons (C u3 u6) u7)) (time (C u4 u5))) = true, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_242 : type_LF_227:= (fun   _ u1  _ _ _ _ => (true = true -> (le (timel Nil) (time u1)) = true, (Term id_true nil)::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_248 : type_LF_227:= (fun  u7  _ u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (timel (Cons (C u3 u6) u7)) (time (C u4 u5))) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil))::nil))::(Term id_true nil)::nil)).
Definition F_255 : type_LF_227:= (fun   _ u1  _ _ _ _ => ((le (timel Nil) (time u1)) = true, (Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_258 : type_LF_227:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (timel (Cons (C u3 u6) u7)) u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_261 : type_LF_227:= (fun   _ u1  _ _ _ _ => ((le 0 (time u1)) = true, (Term id_le ((Term id_0 nil):: (Term id_time ((model_OBJ u1)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_267 : type_LF_227:= (fun   _  _  _ _ _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).
Definition F_264 : type_LF_227:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le (time (C u3 u6)) u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u3):: (model_nat u6)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::nil)).
Definition F_270 : type_LF_227:= (fun  u7  _ u3 u4 u6 _ => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (le u3 u4) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::nil)).

Definition LF_227 := [F_227, F_254, F_242, F_248, F_255, F_258, F_261, F_267, F_264, F_270].


Function f_227 (u2: PLAN) (u1: OBJ) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons (C u3 u6) u7), (C u4 u5) => true
end.

Lemma main_227 : forall F, In F LF_227 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, (forall F', In F' LF_227 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, less (snd (F' e1 e2 e3 e4 e5 e6)) (snd (F u1 u2 u3 u4 u5 u6)) -> fst (F' e1 e2 e3 e4 e5 e6)) -> fst (F u1 u2 u3 u4 u5 u6).
Proof.
intros F HF u1 u2 u3 u4 u5 u6; case_In HF; intro Hind.

	(* GENERATE on [ 227 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_227 u2 u1). apply f_227_ind.

(* case [ 242 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_242). clear HFabs0.
assert (HFabs0 : fst (F_242 Nil _u1 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_242. unfold F_227. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_227. unfold F_242.
auto.



intros _u2 _u1. intro u3. intro u6. intro u7.  intro eq_1. intro u4. intro u5.  intro eq_2.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 248 ] *)

assert (Hind := HFabs0 F_248). clear HFabs0.
assert (HFabs0 : fst (F_248 u7 (C 0 0 ) u3 u4 u5 u6)).
apply Hind. trivial_in 3. unfold snd. unfold F_248. unfold F_227. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_227. unfold F_248. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 254 ] *)

assert (Hind := HFabs0 F_254). clear HFabs0.
assert (HFabs0 : fst (F_254 u7 (C 0 0 ) u3 u4 u5 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_254. unfold F_227. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_227. unfold F_254. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 254 ] *)

unfold fst. unfold F_254. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 242 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (H := Hind F_255). 
assert (HFabs0 : fst (F_255 Nil u1 0 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_255. unfold F_242. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_242. unfold F_255.

unfold fst in HFabs0. unfold F_255 in HFabs0.
auto.



	(* REWRITING on [ 248 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_258). clear Hind.
assert (HFabs1 : fst (F_258 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 5. unfold snd. unfold F_258. unfold F_248. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_248. unfold fst in HFabs1. unfold F_258 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 255 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (Res := Hind F_261). clear Hind.
assert (HFabs1 : fst (F_261 Nil u1 0 0 0 0)).
apply Res. trivial_in 6. unfold snd. unfold F_261. unfold F_255. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_255. unfold fst in HFabs1. unfold F_261 in HFabs1.    simpl. auto.



	(* REWRITING on [ 258 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_264). clear Hind.
assert (HFabs1 : fst (F_264 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 8. unfold snd. unfold F_264. unfold F_258. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_258. unfold fst in HFabs1. unfold F_264 in HFabs1.   
pattern (C u3 u6), u7. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 261 ] *)

rename u1 into d_u1. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. 
assert (Res := Hind F_267). clear Hind.
assert (HFabs1 : fst (F_267 Nil (C 0 0 ) 0 0 0 0)).
apply Res. trivial_in 7. unfold snd. unfold F_267. unfold F_261. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_261. unfold fst in HFabs1. unfold F_267 in HFabs1.   
pattern (time u1). simpl (le _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 267 ] *)

unfold fst. unfold F_267.
auto.



	(* REWRITING on [ 264 ] *)

rename u1 into _u7. rename u2 into d_u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. 
rename _u7 into u7. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_270). clear Hind.
assert (HFabs1 : fst (F_270 u7 (C 0 0 ) u3 u4 u6 0)).
apply Res. trivial_in 9. unfold snd. unfold F_270. unfold F_264. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_264. unfold fst in HFabs1. unfold F_270 in HFabs1.   
pattern u3, u6. simpl (time _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 270 ] *)

unfold fst. unfold F_270.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_227 := fun f => exists F, In F LF_227 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, f = F e1 e2 e3 e4 e5 e6.

Theorem all_true_227: forall F, In F LF_227 -> forall u1: PLAN, forall u2: OBJ, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, fst (F u1 u2 u3  u4  u5  u6).
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


Theorem true_227: forall (u2: PLAN) (u1: OBJ), (sortedT (Cons u1 u2)) = true -> (le (timel u2) (time u1)) = true.
Proof.
do 2 intro.
apply (all_true_227 F_227);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_271 :=  PLAN ->  nat ->  nat ->  nat ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_271 : type_LF_271:= (fun   u1 u2 u3 u4 _ _ _ _ => ((sortedT u1) = true -> (le u2 u3) = true -> (progAt (insAt u1 u2 u4) u3) = u4, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((model_PLAN u1):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_318 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => (false = true -> (le u2 u3) = true -> (le u5 u6) = false -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = u4, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_300 : type_LF_271:= (fun    _ u2 u3 u4 _ _ _ _ => (true = true -> (le u2 u3) = true -> (progAt (insAt Nil u2 u4) u3) = u4, (Term id_true nil)::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Nil nil):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_306 : type_LF_271:= (fun    _ u2 u3 u4 u6 u7 _ _ => (true = true -> (le u2 u3) = true -> (progAt (insAt (Cons (C u6 u7) Nil) u2 u4) u3) = u4, (Term id_true nil)::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_319 : type_LF_271:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = true -> (progAt (insAt Nil u2 u4) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Nil nil):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_312 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((sortedT (Cons (C u5 u8) u9)) = true -> (le u2 u3) = true -> (le u5 u6) = true -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = u4, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_354 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) (time (C u5 u8))) = true -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil))::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_323 : type_LF_271:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = true -> (progAt (Cons (C u2 u4) Nil) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_405 : type_LF_271:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = true -> (le (time (C u2 u4)) u3) = true -> (er (C u2 u4)) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u4)::nil)).
Definition F_409 : type_LF_271:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = true -> (le (time (C u2 u4)) u3) = false -> (progAt Nil u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Nil nil):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_412 : type_LF_271:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = true -> (le u2 u3) = true -> (er (C u2 u4)) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u4)::nil)).
Definition F_418 : type_LF_271:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = true -> (le u2 u3) = true -> u4 = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(model_nat u4)::nil)).
Definition F_415 : type_LF_271:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = true -> (le (time (C u2 u4)) u3) = false -> 0 = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_0 nil)::(model_nat u4)::nil)).
Definition F_421 : type_LF_271:= (fun    _ u2 u3 u4 _ _ _ _ => ((le u2 u3) = true -> (le u2 u3) = false -> 0 = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_0 nil)::(model_nat u4)::nil)).
Definition F_320 : type_LF_271:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = true -> (progAt (insAt (Cons (C u6 u7) Nil) u2 u4) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_456 : type_LF_271:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = true -> (le (time (C u6 u7)) u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) Nil)) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_460 : type_LF_271:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = true -> (le (time (C u6 u7)) u2) = false -> (progAt (insAt Nil u2 u4) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Nil nil):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_466 : type_LF_271:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = true -> (le (time (C u6 u7)) u2) = false -> (progAt (Cons (C u2 u4) Nil) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_357 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (progAt (insAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u2 u4) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_521 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le (time (C u6 u7)) u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) (Cons (C u5 u8) u9))) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil))::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_525 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le (time (C u6 u7)) u2) = false -> (progAt (insAt (Cons (C u5 u8) u9) u2 u4) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_463 : type_LF_271:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = true -> (le u6 u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) Nil)) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_580 : type_LF_271:= (fun    _ u2 u3 u4 u6 _ _ _ => ((le u2 u3) = true -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = true -> (er (C u2 u4)) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u4)::nil)).
Definition F_584 : type_LF_271:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = true -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = false -> (progAt (Cons (C u6 u7) Nil) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_587 : type_LF_271:= (fun    _ u2 u3 u4 u6 _ _ _ => ((le u2 u3) = true -> (le u6 u2) = true -> (le u2 u3) = true -> (er (C u2 u4)) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u4)::nil)).
Definition F_593 : type_LF_271:= (fun    _ u2 u3 u4 u6 _ _ _ => ((le u2 u3) = true -> (le u6 u2) = true -> (le u2 u3) = true -> u4 = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(model_nat u4)::nil)).
Definition F_590 : type_LF_271:= (fun    _ u2 u3 u4 u6 u7 _ _ => ((le u2 u3) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (progAt (Cons (C u6 u7) Nil) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_528 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u6 u7) (Cons (C u5 u8) u9))) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil))::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_628 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 _ _ => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = true -> (er (C u2 u4)) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u4)::nil)).
Definition F_632 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = true -> (le (time (C u2 u4)) u3) = false -> (progAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_635 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 _ _ => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = true -> (le u2 u3) = true -> (er (C u2 u4)) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u4)::nil)).
Definition F_641 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 _ _ => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = true -> (le u2 u3) = true -> u4 = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(model_nat u4)::nil)).
Definition F_638 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u7 u8 => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = true -> (le u2 u3) = false -> (progAt (Cons (C u6 u7) (Cons (C u5 u8) u9)) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_531 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = false -> (progAt (insAt (Cons (C u5 u8) u9) u2 u4) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_670 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = false -> (le (time (C u5 u8)) u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u5 u8) u9)) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_674 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = false -> (le (time (C u5 u8)) u2) = false -> (progAt (insAt u9 u2 u4) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u5):: (model_nat u8)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_insAt ((model_PLAN u9):: (model_nat u2):: (model_nat u4)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_677 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (progAt (Cons (C u2 u4) (Cons (C u5 u8) u9)) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u4)::nil)):: (Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil))::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_727 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 _ _ => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le (time (C u2 u4)) u3) = true -> (er (C u2 u4)) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u4)::nil)).
Definition F_731 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le (time (C u2 u4)) u3) = false -> (progAt (Cons (C u5 u8) u9) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil)):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).
Definition F_734 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 _ _ => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = true -> (er (C u2 u4)) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u2):: (model_nat u4)::nil))::nil))::(model_nat u4)::nil)).
Definition F_740 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 _ _ => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = true -> u4 = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(model_nat u4)::(model_nat u4)::nil)).
Definition F_737 : type_LF_271:= (fun   u9 u2 u3 u4 u5 u6 u8 _ => ((le u2 u3) = true -> (le u5 u6) = true -> (sortedT u9) = true -> (le (timel u9) u5) = true -> (le u6 u2) = false -> (le u5 u2) = true -> (le u2 u3) = false -> (progAt (Cons (C u5 u8) u9) u3) = u4, (Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_true nil)::(Term id_le ((model_nat u5):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u9)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u9)::nil)):: (model_nat u5)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u5):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u2):: (model_nat u3)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u5):: (model_nat u8)::nil)):: (model_PLAN u9)::nil)):: (model_nat u3)::nil))::(model_nat u4)::nil)).

Definition LF_271 := [F_271, F_318, F_300, F_306, F_319, F_312, F_354, F_323, F_405, F_409, F_412, F_418, F_415, F_421, F_320, F_456, F_460, F_466, F_357, F_521, F_525, F_463, F_580, F_584, F_587, F_593, F_590, F_528, F_628, F_632, F_635, F_641, F_638, F_531, F_670, F_674, F_677, F_727, F_731, F_734, F_740, F_737].


Function f_271 (u1: PLAN) {struct u1} : bool :=
 match u1 with
| Nil => true
| (Cons (C u6 u7) Nil) => true
| (Cons (C u6 u7) (Cons (C u5 u8) u9)) => true
end.

Lemma main_271 : forall F, In F LF_271 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, forall u7, forall u8, (forall F', In F' LF_271 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, forall e7, forall e8, less (snd (F' e1 e2 e3 e4 e5 e6 e7 e8)) (snd (F u1 u2 u3 u4 u5 u6 u7 u8)) -> fst (F' e1 e2 e3 e4 e5 e6 e7 e8)) -> fst (F u1 u2 u3 u4 u5 u6 u7 u8).
Proof.
intros F HF u1 u2 u3 u4 u5 u6 u7 u8; case_In HF; intro Hind.

	(* GENERATE on [ 271 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 

revert Hind.

pattern u1, (f_271 u1). apply f_271_ind.

(* case [ 300 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_300). clear HFabs0.
assert (HFabs0 : fst (F_300 Nil u2 u3 u4 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_300. unfold F_271. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_271. unfold F_300.
auto.


(* case [ 306 ] *)

intros _u1. intro u6. intro u7.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_306). clear HFabs0.
assert (HFabs0 : fst (F_306 Nil u2 u3 u4 u6 u7 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_306. unfold F_271. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_271. unfold F_306.
auto.



intros _u1. intro u6. intro u7. intro u5. intro u8. intro u9.  intro eq_1.  intro HFabs0.
case_eq (le u5 u6); [intro H | intro H].

(* case [ 312 ] *)

assert (Hind := HFabs0 F_312). clear HFabs0.
assert (HFabs0 : fst (F_312 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Hind. trivial_in 5. unfold snd. unfold F_312. unfold F_271. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_271. unfold F_312. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 318 ] *)

assert (Hind := HFabs0 F_318). clear HFabs0.
assert (HFabs0 : fst (F_318 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Hind. trivial_in 1. unfold snd. unfold F_318. unfold F_271. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_271. unfold F_318. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 318 ] *)

unfold fst. unfold F_318. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 300 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (H := Hind F_319). 
assert (HFabs0 : fst (F_319 Nil u2 u3 u4 0 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_319. unfold F_300. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_300. unfold F_319.

unfold fst in HFabs0. unfold F_319 in HFabs0.
auto.



	(* NEGATIVE DECOMPOSITION on [ 306 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (H := Hind F_320). 
assert (HFabs0 : fst (F_320 Nil u2 u3 u4 u6 u7 0 0)).
apply H. trivial_in 14. unfold snd. unfold F_320. unfold F_306. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_306. unfold F_320.

unfold fst in HFabs0. unfold F_320 in HFabs0.
auto.



	(* REWRITING on [ 319 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_323). clear Hind.
assert (HFabs1 : fst (F_323 Nil u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 7. unfold snd. unfold F_323. unfold F_319. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_319. unfold fst in HFabs1. unfold F_323 in HFabs1.   
pattern u2, u4. simpl (insAt _ _ _). cbv beta.
 simpl. auto.



	(* AUGMENTATION on [ 312 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H := Hind F_354). clear Hind.
assert (HFabs0: fst (F_354 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H. trivial_in 6. unfold snd. unfold F_312. unfold F_354. rewrite_model. abstract solve_rpo_mul.

unfold fst. unfold F_312.

specialize true_227 with (u1 := (C u5 u8)) (u2 := u9).
specialize true_196 with (u1 := (C u5 u8)) (u2 := u9). auto.




	(* REWRITING on [ 354 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_357). clear Hind.
assert (HFabs1 : fst (F_357 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 18. unfold snd. unfold F_357. unfold F_354. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_354. unfold fst in HFabs1. unfold F_357 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 323 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (H: ((le (time (C u2 u4)) u3) = true) \/ ((le (time (C u2 u4)) u3) = false)). 

destruct ((le (time (C u2 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_405). clear Hind.
assert (HFabs0 : fst (F_405 Nil u2 u3 u4 0 0 0 0)).
apply H1. trivial_in 8. unfold snd. unfold F_405. unfold F_323. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_323. unfold F_405. unfold fst in HFabs0. unfold F_405 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern Nil.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_409). clear Hind.
assert (HFabs0 : fst (F_409 Nil u2 u3 u4 0 0 0 0)).
apply H1. trivial_in 9. unfold snd. unfold F_409. unfold F_323. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_323. unfold F_409. unfold fst in HFabs0. unfold F_409 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern Nil.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 405 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_412). clear Hind.
assert (HFabs1 : fst (F_412 Nil u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 10. unfold snd. unfold F_412. unfold F_405. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_405. unfold fst in HFabs1. unfold F_412 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 409 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_415). clear Hind.
assert (HFabs1 : fst (F_415 Nil u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 12. unfold snd. unfold F_415. unfold F_409. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_409. unfold fst in HFabs1. unfold F_415 in HFabs1.   
pattern u3. simpl (progAt _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 412 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_418). clear Hind.
assert (HFabs1 : fst (F_418 Nil u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 11. unfold snd. unfold F_418. unfold F_412. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_412. unfold fst in HFabs1. unfold F_418 in HFabs1.   
pattern u2, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 418 ] *)

unfold fst. unfold F_418.
auto.



	(* REWRITING on [ 415 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_421). clear Hind.
assert (HFabs1 : fst (F_421 Nil u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 13. unfold snd. unfold F_421. unfold F_415. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_415. unfold fst in HFabs1. unfold F_421 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 421 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
unfold fst. unfold F_421. specialize true_158 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 320 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u6 u7)) u2) = true) \/ ((le (time (C u6 u7)) u2) = false)). 

destruct ((le (time (C u6 u7)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 131 ] *)

assert (H1 := Hind F_456). clear Hind.
assert (HFabs0 : fst (F_456 Nil u2 u3 u4 u6 u7 0 0)).
apply H1. trivial_in 15. unfold snd. unfold F_456. unfold F_320. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_320. unfold F_456. unfold fst in HFabs0. unfold F_456 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern Nil.
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 132 ] *)

assert (H1 := Hind F_460). clear Hind.
assert (HFabs0 : fst (F_460 Nil u2 u3 u4 u6 u7 0 0)).
apply H1. trivial_in 16. unfold snd. unfold F_460. unfold F_320. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_320. unfold F_460. unfold fst in HFabs0. unfold F_460 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern Nil.
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 456 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_463). clear Hind.
assert (HFabs1 : fst (F_463 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 21. unfold snd. unfold F_463. unfold F_456. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_456. unfold fst in HFabs1. unfold F_463 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 460 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_466). clear Hind.
assert (HFabs1 : fst (F_466 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 17. unfold snd. unfold F_466. unfold F_460. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_460. unfold fst in HFabs1. unfold F_466 in HFabs1.   
pattern u2, u4. simpl (insAt _ _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 466 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_323). clear Hind.
assert (HFabs1 : fst (F_323 Nil u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 7. unfold snd. unfold F_323. unfold F_466. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_466. unfold fst in HFabs1. unfold F_323 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 357 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u6 u7)) u2) = true) \/ ((le (time (C u6 u7)) u2) = false)). 

destruct ((le (time (C u6 u7)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 131 ] *)

assert (H1 := Hind F_521). clear Hind.
assert (HFabs0 : fst (F_521 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 19. unfold snd. unfold F_521. unfold F_357. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_357. unfold F_521. unfold fst in HFabs0. unfold F_521 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern (Cons (C u5 u8) u9).
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 132 ] *)

assert (H1 := Hind F_525). clear Hind.
assert (HFabs0 : fst (F_525 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 20. unfold snd. unfold F_525. unfold F_357. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_357. unfold F_525. unfold fst in HFabs0. unfold F_525 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern (Cons (C u5 u8) u9).
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 521 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_528). clear Hind.
assert (HFabs1 : fst (F_528 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 27. unfold snd. unfold F_528. unfold F_521. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_521. unfold fst in HFabs1. unfold F_528 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 525 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_531). clear Hind.
assert (HFabs1 : fst (F_531 u9 u2 u3 u4 u5 u6 u8 0)).
apply Res. trivial_in 33. unfold snd. unfold F_531. unfold F_525. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_525. unfold fst in HFabs1. unfold F_531 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 463 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u2 u4)) u3) = true) \/ ((le (time (C u2 u4)) u3) = false)). 

destruct ((le (time (C u2 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_580). clear Hind.
assert (HFabs0 : fst (F_580 Nil u2 u3 u4 u6 0 0 0)).
apply H1. trivial_in 22. unfold snd. unfold F_580. unfold F_463. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_463. unfold F_580. unfold fst in HFabs0. unfold F_580 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) Nil).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_584). clear Hind.
assert (HFabs0 : fst (F_584 Nil u2 u3 u4 u6 u7 0 0)).
apply H1. trivial_in 23. unfold snd. unfold F_584. unfold F_463. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_463. unfold F_584. unfold fst in HFabs0. unfold F_584 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) Nil).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 580 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_587). clear Hind.
assert (HFabs1 : fst (F_587 Nil u2 u3 u4 u6 0 0 0)).
apply Res. trivial_in 24. unfold snd. unfold F_587. unfold F_580. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_580. unfold fst in HFabs1. unfold F_587 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 584 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_590). clear Hind.
assert (HFabs1 : fst (F_590 Nil u2 u3 u4 u6 u7 0 0)).
apply Res. trivial_in 26. unfold snd. unfold F_590. unfold F_584. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_584. unfold fst in HFabs1. unfold F_590 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 587 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. 
assert (Res := Hind F_593). clear Hind.
assert (HFabs1 : fst (F_593 Nil u2 u3 u4 u6 0 0 0)).
apply Res. trivial_in 25. unfold snd. unfold F_593. unfold F_587. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_587. unfold fst in HFabs1. unfold F_593 in HFabs1.   
pattern u2, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 593 ] *)

unfold fst. unfold F_593.
auto.



	(* SUBSUMPTION on [ 590 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u6. rename u6 into _u7. rename u7 into d_u7. rename u8 into d_u8. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. 
unfold fst. unfold F_590. specialize true_158 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 528 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (H: ((le (time (C u2 u4)) u3) = true) \/ ((le (time (C u2 u4)) u3) = false)). 

destruct ((le (time (C u2 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_628). clear Hind.
assert (HFabs0 : fst (F_628 u9 u2 u3 u4 u5 u6 0 0)).
apply H1. trivial_in 28. unfold snd. unfold F_628. unfold F_528. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_528. unfold F_628. unfold fst in HFabs0. unfold F_628 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) (Cons (C u5 u8) u9)).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_632). clear Hind.
assert (HFabs0 : fst (F_632 u9 u2 u3 u4 u5 u6 u7 u8)).
apply H1. trivial_in 29. unfold snd. unfold F_632. unfold F_528. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_528. unfold F_632. unfold fst in HFabs0. unfold F_632 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u6 u7) (Cons (C u5 u8) u9)).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 628 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_635). clear Hind.
assert (HFabs1 : fst (F_635 u9 u2 u3 u4 u5 u6 0 0)).
apply Res. trivial_in 30. unfold snd. unfold F_635. unfold F_628. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_628. unfold fst in HFabs1. unfold F_635 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 632 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
assert (Res := Hind F_638). clear Hind.
assert (HFabs1 : fst (F_638 u9 u2 u3 u4 u5 u6 u7 u8)).
apply Res. trivial_in 32. unfold snd. unfold F_638. unfold F_632. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_632. unfold fst in HFabs1. unfold F_638 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 635 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_641). clear Hind.
assert (HFabs1 : fst (F_641 u9 u2 u3 u4 u5 u6 0 0)).
apply Res. trivial_in 31. unfold snd. unfold F_641. unfold F_635. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_635. unfold fst in HFabs1. unfold F_641 in HFabs1.   
pattern u2, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 641 ] *)

unfold fst. unfold F_641.
auto.



	(* SUBSUMPTION on [ 638 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. 
unfold fst. unfold F_638. specialize true_158 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 531 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (H: ((le (time (C u5 u8)) u2) = true) \/ ((le (time (C u5 u8)) u2) = false)). 

destruct ((le (time (C u5 u8)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 131 ] *)

assert (H1 := Hind F_670). clear Hind.
assert (HFabs0 : fst (F_670 u9 u2 u3 u4 u5 u6 u8 0)).
apply H1. trivial_in 34. unfold snd. unfold F_670. unfold F_531. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_531. unfold F_670. unfold fst in HFabs0. unfold F_670 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u2.
pattern u9.
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 132 ] *)

assert (H1 := Hind F_674). clear Hind.
assert (HFabs0 : fst (F_674 u9 u2 u3 u4 u5 u6 u8 0)).
apply H1. trivial_in 35. unfold snd. unfold F_674. unfold F_531. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_531. unfold F_674. unfold fst in HFabs0. unfold F_674 in HFabs0. simpl in HFabs0. 
pattern (C u5 u8).
pattern u2.
pattern u9.
pattern u4.
simpl (insAt _ _ _). cbv beta. try unfold insAt. try rewrite H. try rewrite H0. try unfold insAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 670 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_677). clear Hind.
assert (HFabs1 : fst (F_677 u9 u2 u3 u4 u5 u6 u8 0)).
apply Res. trivial_in 36. unfold snd. unfold F_677. unfold F_670. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_670. unfold fst in HFabs1. unfold F_677 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 674 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_271). clear Hind.
assert (HFabs1 : fst (F_271 u9 u2 u3 u4 0 0 0 0)).
apply Res. trivial_in 0. unfold snd. unfold F_271. unfold F_674. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_674. unfold fst in HFabs1. unfold F_271 in HFabs1.   
pattern u5, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 677 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (H: ((le (time (C u2 u4)) u3) = true) \/ ((le (time (C u2 u4)) u3) = false)). 

destruct ((le (time (C u2 u4)) u3)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_727). clear Hind.
assert (HFabs0 : fst (F_727 u9 u2 u3 u4 u5 u6 0 0)).
apply H1. trivial_in 37. unfold snd. unfold F_727. unfold F_677. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_677. unfold F_727. unfold fst in HFabs0. unfold F_727 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_731). clear Hind.
assert (HFabs0 : fst (F_731 u9 u2 u3 u4 u5 u6 u8 0)).
apply H1. trivial_in 38. unfold snd. unfold F_731. unfold F_677. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_677. unfold F_731. unfold fst in HFabs0. unfold F_731 in HFabs0. simpl in HFabs0. 
pattern (C u2 u4).
pattern u3.
pattern (Cons (C u5 u8) u9).
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 727 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_734). clear Hind.
assert (HFabs1 : fst (F_734 u9 u2 u3 u4 u5 u6 0 0)).
apply Res. trivial_in 39. unfold snd. unfold F_734. unfold F_727. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_727. unfold fst in HFabs1. unfold F_734 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 731 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
assert (Res := Hind F_737). clear Hind.
assert (HFabs1 : fst (F_737 u9 u2 u3 u4 u5 u6 u8 0)).
apply Res. trivial_in 41. unfold snd. unfold F_737. unfold F_731. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_731. unfold fst in HFabs1. unfold F_737 in HFabs1.   
pattern u2, u4. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 734 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into d_u7. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_740). clear Hind.
assert (HFabs1 : fst (F_740 u9 u2 u3 u4 u5 u6 0 0)).
apply Res. trivial_in 40. unfold snd. unfold F_740. unfold F_734. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_734. unfold fst in HFabs1. unfold F_740 in HFabs1.   
pattern u2, u4. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 740 ] *)

unfold fst. unfold F_740.
auto.



	(* SUBSUMPTION on [ 737 ] *)

rename u1 into _u9. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. rename u7 into _u8. rename u8 into d_u8. 
rename _u9 into u9. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. rename _u8 into u8. 
unfold fst. unfold F_737. specialize true_158 with (u1 := u2) (u2 := u3). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_271 := fun f => exists F, In F LF_271 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, exists e7, exists e8, f = F e1 e2 e3 e4 e5 e6 e7 e8.

Theorem all_true_271: forall F, In F LF_271 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, forall u7: nat, forall u8: nat, fst (F u1 u2  u3  u4  u5  u6  u7  u8).
Proof.
let n := constr:(8) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_271);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_271;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_271: forall (u1: PLAN) (u2: nat) (u3: nat) (u4: nat), (sortedT u1) = true -> (le u2 u3) = true -> (progAt (insAt u1 u2 u4) u3) = u4.
Proof.
do 4 intro.
apply (all_true_271 F_271);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
