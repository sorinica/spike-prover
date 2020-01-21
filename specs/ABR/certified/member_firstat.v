
Require Import member_firstat_spec.



Definition type_LF_157 :=  nat -> (Prop * (List.list term)).

Definition F_157 : type_LF_157:= (fun    u1 => ((nat_eq u1 u1) = false -> False, (Term id_nat_eq ((model_nat u1):: (model_nat u1)::nil))::(Term id_false nil)::nil)).
Definition F_169 : type_LF_157:= (fun     _ => (true = false -> False, (Term id_true nil)::(Term id_false nil)::nil)).

Definition LF_157 := [F_157, F_169].


Function f_157 (u1: nat) {struct u1} : bool :=
 match u1 with
| 0 => true
| (S u2) => true
end.

Lemma main_157 : forall F, In F LF_157 -> forall u1, (forall F', In F' LF_157 -> forall e1, less (snd (F' e1)) (snd (F u1)) -> fst (F' e1)) -> fst (F u1).
Proof.
intros F HF u1; case_In HF; intro Hind.

	(* GENERATE on [ 157 ] *)

rename u1 into _u1. 
rename _u1 into u1. 

revert Hind.

pattern u1, (f_157 u1). apply f_157_ind.

(* case [ 169 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_169). clear HFabs0.
assert (HFabs0 : fst (F_169 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_169. unfold F_157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_157. unfold F_169.
auto.


(* case [ 175 ] *)

intros _u1. intro u2.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_157). clear HFabs0.
assert (HFabs0 : fst (F_157 u2)).
apply Hind. trivial_in 0. unfold snd. unfold F_157. unfold F_157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_157. unfold F_157.
auto.





	(* NEGATIVE CLASH on [ 169 ] *)

unfold fst. unfold F_169. intros. try discriminate.



Qed.



(* the set of all formula instances from the proof *)
Definition S_157 := fun f => exists F, In F LF_157 /\ exists e1, f = F e1.

Theorem all_true_157: forall F, In F LF_157 -> forall u1: nat, fst (F u1).
Proof.
let n := constr:(1) in
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


Theorem true_157: forall (u1: nat), (nat_eq u1 u1) = false -> False.
Proof.
do 1 intro.
apply (all_true_157 F_157);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_179 :=  nat ->  nat -> (Prop * (List.list term)).

Definition F_179 : type_LF_179:= (fun    u1 u2 => ((le u1 u2) = false -> (le u1 u2) = true -> False, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_195 : type_LF_179:= (fun    u2 _ => (true = false -> (le 0 u2) = true -> False, (Term id_true nil)::(Term id_false nil)::(Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_201 : type_LF_179:= (fun    u3 _ => (false = false -> (le (S u3) 0) = true -> False, (Term id_false nil)::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_207 : type_LF_179:= (fun    u3 u4 => ((le u3 u4) = false -> (le (S u3) (S u4)) = true -> False, (Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_S ((model_nat u4)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_208 : type_LF_179:= (fun    u3 _ => ((le (S u3) 0) = true -> False, (Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_214 : type_LF_179:= (fun     _ _ => (false = true -> False, (Term id_false nil)::(Term id_true nil)::nil)).

Definition LF_179 := [F_179, F_195, F_201, F_207, F_208, F_214].


Function f_179 (u1: nat) (u2: nat) {struct u1} : bool :=
 match u1, u2 with
| 0, _ => true
| (S u3), 0 => true
| (S u3), (S u4) => true
end.

Lemma main_179 : forall F, In F LF_179 -> forall u1, forall u2, (forall F', In F' LF_179 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 179 ] *)

rename u1 into _u1. rename u2 into _u2. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_179 u1 u2). apply f_179_ind.

(* case [ 195 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_195). clear HFabs0.
assert (HFabs0 : fst (F_195 _u2 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_195. unfold F_179. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_179. unfold F_195.
auto.


(* case [ 201 ] *)

intros _u1 _u2. intro u3.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_201). clear HFabs0.
assert (HFabs0 : fst (F_201 u3 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_201. unfold F_179. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_179. unfold F_201.
auto.


(* case [ 207 ] *)

intros _u1 _u2. intro u3.  intro eq_1. intro u4.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_207). clear HFabs0.
assert (HFabs0 : fst (F_207 u3 u4)).
apply Hind. trivial_in 3. unfold snd. unfold F_207. unfold F_179. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_179. unfold F_207.
auto.





	(* NEGATIVE CLASH on [ 195 ] *)

unfold fst. unfold F_195. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 201 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (H := Hind F_208). 
assert (HFabs0 : fst (F_208 u3 0)).
apply H. trivial_in 4. unfold snd. unfold F_208. unfold F_201. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_201. unfold F_208.

unfold fst in HFabs0. unfold F_208 in HFabs0.
auto.



	(* REWRITING on [ 207 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_179). clear Hind.
assert (HFabs1 : fst (F_179 u3 u4)).
apply Res. trivial_in 0. unfold snd. unfold F_179. unfold F_207. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_207. unfold fst in HFabs1. unfold F_179 in HFabs1.   
pattern u3, u4. simpl (le _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 208 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (Res := Hind F_214). clear Hind.
assert (HFabs1 : fst (F_214 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_214. unfold F_208. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_208. unfold fst in HFabs1. unfold F_214 in HFabs1.   
pattern u3. simpl (le _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE CLASH on [ 214 ] *)

unfold fst. unfold F_214. intros. try discriminate.



Qed.



(* the set of all formula instances from the proof *)
Definition S_179 := fun f => exists F, In F LF_179 /\ exists e1, exists e2, f = F e1 e2.

Theorem all_true_179: forall F, In F LF_179 -> forall u1: nat, forall u2: nat, fst (F u1  u2).
Proof.
let n := constr:(2) in
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


Theorem true_179: forall (u1: nat) (u2: nat), (le u1 u2) = false -> (le u1 u2) = true -> False.
Proof.
do 2 intro.
apply (all_true_179 F_179);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_219 :=  PLAN ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_219 : type_LF_219:= (fun   u1 u2 _ _ => ((PLAN_eq (listAt u1 u2) Nil) = false -> (memberC (firstAt u1 u2) u1) = true, (Term id_PLAN_eq ((Term id_listAt ((model_PLAN u1):: (model_nat u2)::nil)):: (Term id_Nil nil)::nil))::(Term id_false nil)::(Term id_memberC ((Term id_firstAt ((model_PLAN u1):: (model_nat u2)::nil)):: (model_PLAN u1)::nil))::(Term id_true nil)::nil)).
Definition F_233 : type_LF_219:= (fun    _ u2 _ _ => ((PLAN_eq Nil Nil) = false -> (memberC (firstAt Nil u2) Nil) = true, (Term id_PLAN_eq ((Term id_Nil nil):: (Term id_Nil nil)::nil))::(Term id_false nil)::(Term id_memberC ((Term id_firstAt ((Term id_Nil nil):: (model_nat u2)::nil)):: (Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_248 : type_LF_219:= (fun    _ u2 _ _ => (true = false -> (memberC (firstAt Nil u2) Nil) = true, (Term id_true nil)::(Term id_false nil)::(Term id_memberC ((Term id_firstAt ((Term id_Nil nil):: (model_nat u2)::nil)):: (Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_239 : type_LF_219:= (fun   u5 u2 u6 u7 => ((PLAN_eq (Cons (C u6 u7) u5) Nil) = false -> (le (time (C u6 u7)) u2) = true -> (memberC (firstAt (Cons (C u6 u7) u5) u2) (Cons (C u6 u7) u5)) = true, (Term id_PLAN_eq ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil)):: (Term id_Nil nil)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_memberC ((Term id_firstAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil)):: (model_nat u2)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_251 : type_LF_219:= (fun   u5 u2 u6 u7 => (false = false -> (le (time (C u6 u7)) u2) = true -> (memberC (firstAt (Cons (C u6 u7) u5) u2) (Cons (C u6 u7) u5)) = true, (Term id_false nil)::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_memberC ((Term id_firstAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil)):: (model_nat u2)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_245 : type_LF_219:= (fun   u5 u2 u6 u7 => ((PLAN_eq (listAt u5 u2) Nil) = false -> (le (time (C u6 u7)) u2) = false -> (memberC (firstAt (Cons (C u6 u7) u5) u2) (Cons (C u6 u7) u5)) = true, (Term id_PLAN_eq ((Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil)):: (Term id_Nil nil)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_memberC ((Term id_firstAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil)):: (model_nat u2)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_252 : type_LF_219:= (fun   u5 u2 u6 u7 => ((le (time (C u6 u7)) u2) = true -> (memberC (firstAt (Cons (C u6 u7) u5) u2) (Cons (C u6 u7) u5)) = true, (Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_memberC ((Term id_firstAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil)):: (model_nat u2)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_255 : type_LF_219:= (fun   u5 u2 u6 u7 => ((PLAN_eq (listAt u5 u2) Nil) = false -> (le u6 u2) = false -> (memberC (firstAt (Cons (C u6 u7) u5) u2) (Cons (C u6 u7) u5)) = true, (Term id_PLAN_eq ((Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil)):: (Term id_Nil nil)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_memberC ((Term id_firstAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil)):: (model_nat u2)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_271 : type_LF_219:= (fun   u5 u2 u6 u7 => ((PLAN_eq (listAt u5 u2) Nil) = false -> (le u6 u2) = false -> (le (time (C u6 u7)) u2) = true -> (memberC (C u6 u7) (Cons (C u6 u7) u5)) = true, (Term id_PLAN_eq ((Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil)):: (Term id_Nil nil)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_memberC ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_275 : type_LF_219:= (fun   u5 u2 u6 u7 => ((PLAN_eq (listAt u5 u2) Nil) = false -> (le u6 u2) = false -> (le (time (C u6 u7)) u2) = false -> (memberC (firstAt u5 u2) (Cons (C u6 u7) u5)) = true, (Term id_PLAN_eq ((Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil)):: (Term id_Nil nil)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_memberC ((Term id_firstAt ((model_PLAN u5):: (model_nat u2)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_278 : type_LF_219:= (fun   u5 u2 u6 u7 => ((PLAN_eq (listAt u5 u2) Nil) = false -> (le u6 u2) = false -> (le u6 u2) = true -> (memberC (C u6 u7) (Cons (C u6 u7) u5)) = true, (Term id_PLAN_eq ((Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil)):: (Term id_Nil nil)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_memberC ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_281 : type_LF_219:= (fun   u5 u2 u6 u7 => ((PLAN_eq (listAt u5 u2) Nil) = false -> (le u6 u2) = false -> (le u6 u2) = false -> (memberC (firstAt u5 u2) (Cons (C u6 u7) u5)) = true, (Term id_PLAN_eq ((Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil)):: (Term id_Nil nil)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_memberC ((Term id_firstAt ((model_PLAN u5):: (model_nat u2)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_294 : type_LF_219:= (fun   u5 u2 u6 u7 => ((PLAN_eq (listAt u5 u2) Nil) = false -> (le u6 u2) = false -> (le u6 u2) = false -> (OBJ_eq (firstAt u5 u2) (C u6 u7)) = true -> true = true, (Term id_PLAN_eq ((Term id_listAt ((model_PLAN u5):: (model_nat u2)::nil)):: (Term id_Nil nil)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_OBJ_eq ((Term id_firstAt ((model_PLAN u5):: (model_nat u2)::nil)):: (Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_true nil)::nil)).
Definition F_258 : type_LF_219:= (fun   u5 u2 u6 u7 => ((le u6 u2) = true -> (memberC (firstAt (Cons (C u6 u7) u5) u2) (Cons (C u6 u7) u5)) = true, (Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_memberC ((Term id_firstAt ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil)):: (model_nat u2)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_309 : type_LF_219:= (fun   u5 u2 u6 u7 => ((le u6 u2) = true -> (le (time (C u6 u7)) u2) = true -> (memberC (C u6 u7) (Cons (C u6 u7) u5)) = true, (Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_memberC ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_313 : type_LF_219:= (fun   u5 u2 u6 u7 => ((le u6 u2) = true -> (le (time (C u6 u7)) u2) = false -> (memberC (firstAt u5 u2) (Cons (C u6 u7) u5)) = true, (Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_memberC ((Term id_firstAt ((model_PLAN u5):: (model_nat u2)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_319 : type_LF_219:= (fun   u5 u2 u6 u7 => ((le u6 u2) = true -> (le u6 u2) = false -> (memberC (firstAt u5 u2) (Cons (C u6 u7) u5)) = true, (Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_memberC ((Term id_firstAt ((model_PLAN u5):: (model_nat u2)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_316 : type_LF_219:= (fun   u5 u2 u6 u7 => ((le u6 u2) = true -> (le u6 u2) = true -> (memberC (C u6 u7) (Cons (C u6 u7) u5)) = true, (Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_memberC ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_333 : type_LF_219:= (fun    _ u2 u6 u7 => ((le u6 u2) = true -> (le u6 u2) = true -> (OBJ_eq (C u6 u7) (C u6 u7)) = true -> true = true, (Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_OBJ_eq ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_true nil)::nil)).
Definition F_337 : type_LF_219:= (fun   u5 u2 u6 u7 => ((le u6 u2) = true -> (le u6 u2) = true -> (OBJ_eq (C u6 u7) (C u6 u7)) = false -> (memberC (C u6 u7) u5) = true, (Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_OBJ_eq ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (Term id_C ((model_nat u6):: (model_nat u7)::nil))::nil))::(Term id_false nil)::(Term id_memberC ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::(Term id_true nil)::nil)).
Definition F_347 : type_LF_219:= (fun   u5 u2 u6 u7 => ((le u6 u2) = true -> (le u6 u2) = true -> true = false -> (nat_eq u6 u6) = true -> (nat_eq u7 u7) = true -> (memberC (C u6 u7) u5) = true, (Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_true nil)::(Term id_false nil)::(Term id_nat_eq ((model_nat u6):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u7):: (model_nat u7)::nil))::(Term id_true nil)::(Term id_memberC ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::(Term id_true nil)::nil)).
Definition F_351 : type_LF_219:= (fun   u5 u2 u6 u7 => ((le u6 u2) = true -> (le u6 u2) = true -> false = false -> (nat_eq u6 u6) = false -> (memberC (C u6 u7) u5) = true, (Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_false nil)::(Term id_false nil)::(Term id_nat_eq ((model_nat u6):: (model_nat u6)::nil))::(Term id_false nil)::(Term id_memberC ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::(Term id_true nil)::nil)).
Definition F_355 : type_LF_219:= (fun   u5 u2 u6 u7 => ((le u6 u2) = true -> (le u6 u2) = true -> false = false -> (nat_eq u6 u6) = true -> (nat_eq u7 u7) = false -> (memberC (C u6 u7) u5) = true, (Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_false nil)::(Term id_false nil)::(Term id_nat_eq ((model_nat u6):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u7):: (model_nat u7)::nil))::(Term id_false nil)::(Term id_memberC ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::(Term id_true nil)::nil)).
Definition F_356 : type_LF_219:= (fun   u5 u2 u6 u7 => ((le u6 u2) = true -> (le u6 u2) = true -> (nat_eq u6 u6) = false -> (memberC (C u6 u7) u5) = true, (Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u6):: (model_nat u6)::nil))::(Term id_false nil)::(Term id_memberC ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::(Term id_true nil)::nil)).
Definition F_357 : type_LF_219:= (fun   u5 u2 u6 u7 => ((le u6 u2) = true -> (le u6 u2) = true -> (nat_eq u6 u6) = true -> (nat_eq u7 u7) = false -> (memberC (C u6 u7) u5) = true, (Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u6):: (model_nat u6)::nil))::(Term id_true nil)::(Term id_nat_eq ((model_nat u7):: (model_nat u7)::nil))::(Term id_false nil)::(Term id_memberC ((Term id_C ((model_nat u6):: (model_nat u7)::nil)):: (model_PLAN u5)::nil))::(Term id_true nil)::nil)).

Definition LF_219 := [F_219, F_233, F_248, F_239, F_251, F_245, F_252, F_255, F_271, F_275, F_278, F_281, F_294, F_258, F_309, F_313, F_319, F_316, F_333, F_337, F_347, F_351, F_355, F_356, F_357].


Function f_219 (u1: PLAN) (u2: nat) {struct u1} : PLAN :=
 match u1, u2 with
| Nil, _ => Nil
| (Cons (C u6 u7) u5), _ => Nil
end.

Lemma main_219 : forall F, In F LF_219 -> forall u1, forall u2, forall u3, forall u4, (forall F', In F' LF_219 -> forall e1, forall e2, forall e3, forall e4, less (snd (F' e1 e2 e3 e4)) (snd (F u1 u2 u3 u4)) -> fst (F' e1 e2 e3 e4)) -> fst (F u1 u2 u3 u4).
Proof.
intros F HF u1 u2 u3 u4; case_In HF; intro Hind.

	(* GENERATE on [ 219 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_219 u1 u2). apply f_219_ind.

(* case [ 233 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_233). clear HFabs0.
assert (HFabs0 : fst (F_233 Nil _u2 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_233. unfold F_219. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_219. unfold F_233.
auto.



intros _u1 _u2. intro u6. intro u7. intro u5.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
case_eq (le (time (C u6 u7)) _u2); [intro H | intro H].

(* case [ 239 ] *)

assert (Hind := HFabs0 F_239). clear HFabs0.
assert (HFabs0 : fst (F_239 u5 _u2 u6 u7)).
apply Hind. trivial_in 3. unfold snd. unfold F_239. unfold F_219. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_219. unfold F_239. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 245 ] *)

assert (Hind := HFabs0 F_245). clear HFabs0.
assert (HFabs0 : fst (F_245 u5 _u2 u6 u7)).
apply Hind. trivial_in 5. unfold snd. unfold F_245. unfold F_219. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_219. unfold F_245. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* REWRITING on [ 233 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. 
rename _u2 into u2. 
assert (Res := Hind F_248). clear Hind.
assert (HFabs1 : fst (F_248 Nil u2 0 0)).
apply Res. trivial_in 2. unfold snd. unfold F_248. unfold F_233. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_233. unfold fst in HFabs1. unfold F_248 in HFabs1.    simpl. auto.



	(* NEGATIVE CLASH on [ 248 ] *)

unfold fst. unfold F_248. intros. try discriminate.



	(* REWRITING on [ 239 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_251). clear Hind.
assert (HFabs1 : fst (F_251 u5 u2 u6 u7)).
apply Res. trivial_in 4. unfold snd. unfold F_251. unfold F_239. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_239. unfold fst in HFabs1. unfold F_251 in HFabs1.   
pattern (C u6 u7), u5. simpl (PLAN_eq _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE DECOMPOSITION on [ 251 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (H := Hind F_252). 
assert (HFabs0 : fst (F_252 u5 u2 u6 u7)).
apply H. trivial_in 6. unfold snd. unfold F_252. unfold F_251. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_251. unfold F_252.

unfold fst in HFabs0. unfold F_252 in HFabs0.
auto.



	(* REWRITING on [ 245 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_255). clear Hind.
assert (HFabs1 : fst (F_255 u5 u2 u6 u7)).
apply Res. trivial_in 7. unfold snd. unfold F_255. unfold F_245. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_245. unfold fst in HFabs1. unfold F_255 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 252 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_258). clear Hind.
assert (HFabs1 : fst (F_258 u5 u2 u6 u7)).
apply Res. trivial_in 13. unfold snd. unfold F_258. unfold F_252. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_252. unfold fst in HFabs1. unfold F_258 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 255 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u6 u7)) u2) = true) \/ ((le (time (C u6 u7)) u2) = false)). 

destruct ((le (time (C u6 u7)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 143 ] *)

assert (H1 := Hind F_271). clear Hind.
assert (HFabs0 : fst (F_271 u5 u2 u6 u7)).
apply H1. trivial_in 8. unfold snd. unfold F_271. unfold F_255. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_255. unfold F_271. unfold fst in HFabs0. unfold F_271 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern u5.
simpl (firstAt _ _). cbv beta. try unfold firstAt. try rewrite H. try rewrite H0. try unfold firstAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 144 ] *)

assert (H1 := Hind F_275). clear Hind.
assert (HFabs0 : fst (F_275 u5 u2 u6 u7)).
apply H1. trivial_in 9. unfold snd. unfold F_275. unfold F_255. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_255. unfold F_275. unfold fst in HFabs0. unfold F_275 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern u5.
simpl (firstAt _ _). cbv beta. try unfold firstAt. try rewrite H. try rewrite H0. try unfold firstAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 271 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_278). clear Hind.
assert (HFabs1 : fst (F_278 u5 u2 u6 u7)).
apply Res. trivial_in 10. unfold snd. unfold F_278. unfold F_271. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_271. unfold fst in HFabs1. unfold F_278 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 275 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_281). clear Hind.
assert (HFabs1 : fst (F_281 u5 u2 u6 u7)).
apply Res. trivial_in 11. unfold snd. unfold F_281. unfold F_275. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_275. unfold fst in HFabs1. unfold F_281 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 278 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
unfold fst. unfold F_278. specialize true_179 with (u1 := u6) (u2 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 281 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((OBJ_eq (firstAt u5 u2) (C u6 u7)) = true) \/ ((OBJ_eq (firstAt u5 u2) (C u6 u7)) = false)). 

destruct ((OBJ_eq (firstAt u5 u2) (C u6 u7))); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 90 ] *)

assert (H1 := Hind F_294). clear Hind.
assert (HFabs0 : fst (F_294 u5 u2 u6 u7)).
apply H1. trivial_in 12. unfold snd. unfold F_294. unfold F_281. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_281. unfold F_294. unfold fst in HFabs0. unfold F_294 in HFabs0. simpl in HFabs0. 
pattern (firstAt u5 u2).
pattern (C u6 u7).
pattern u5.
simpl (memberC _ _). cbv beta. try unfold memberC. try rewrite H. try rewrite H0. try unfold memberC in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 91 ] *)

assert (H1 := Hind F_219). clear Hind.
assert (HFabs0 : fst (F_219 u5 u2 0 0)).
apply H1. trivial_in 0. unfold snd. unfold F_219. unfold F_281. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_281. unfold F_219. unfold fst in HFabs0. unfold F_219 in HFabs0. simpl in HFabs0. 
pattern (firstAt u5 u2).
pattern (C u6 u7).
pattern u5.
simpl (memberC _ _). cbv beta. try unfold memberC. try rewrite H. try rewrite H0. try unfold memberC in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 294 ] *)

unfold fst. unfold F_294.
auto.



	(* TOTAL CASE REWRITING on [ 258 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((le (time (C u6 u7)) u2) = true) \/ ((le (time (C u6 u7)) u2) = false)). 

destruct ((le (time (C u6 u7)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 143 ] *)

assert (H1 := Hind F_309). clear Hind.
assert (HFabs0 : fst (F_309 u5 u2 u6 u7)).
apply H1. trivial_in 14. unfold snd. unfold F_309. unfold F_258. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_258. unfold F_309. unfold fst in HFabs0. unfold F_309 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern u5.
simpl (firstAt _ _). cbv beta. try unfold firstAt. try rewrite H. try rewrite H0. try unfold firstAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 144 ] *)

assert (H1 := Hind F_313). clear Hind.
assert (HFabs0 : fst (F_313 u5 u2 u6 u7)).
apply H1. trivial_in 15. unfold snd. unfold F_313. unfold F_258. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_258. unfold F_313. unfold fst in HFabs0. unfold F_313 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern u2.
pattern u5.
simpl (firstAt _ _). cbv beta. try unfold firstAt. try rewrite H. try rewrite H0. try unfold firstAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 309 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_316). clear Hind.
assert (HFabs1 : fst (F_316 u5 u2 u6 u7)).
apply Res. trivial_in 17. unfold snd. unfold F_316. unfold F_309. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_309. unfold fst in HFabs1. unfold F_316 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 313 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (Res := Hind F_319). clear Hind.
assert (HFabs1 : fst (F_319 u5 u2 u6 u7)).
apply Res. trivial_in 16. unfold snd. unfold F_319. unfold F_313. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_313. unfold fst in HFabs1. unfold F_319 in HFabs1.   
pattern u6, u7. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 319 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
unfold fst. unfold F_319. specialize true_179 with (u1 := u6) (u2 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 316 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((OBJ_eq (C u6 u7) (C u6 u7)) = true) \/ ((OBJ_eq (C u6 u7) (C u6 u7)) = false)). 

destruct ((OBJ_eq (C u6 u7) (C u6 u7))); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 90 ] *)

assert (H1 := Hind F_333). clear Hind.
assert (HFabs0 : fst (F_333 Nil u2 u6 u7)).
apply H1. trivial_in 18. unfold snd. unfold F_333. unfold F_316. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_316. unfold F_333. unfold fst in HFabs0. unfold F_333 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern (C u6 u7).
pattern u5.
simpl (memberC _ _). cbv beta. try unfold memberC. try rewrite H. try rewrite H0. try unfold memberC in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 91 ] *)

assert (H1 := Hind F_337). clear Hind.
assert (HFabs0 : fst (F_337 u5 u2 u6 u7)).
apply H1. trivial_in 19. unfold snd. unfold F_337. unfold F_316. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_316. unfold F_337. unfold fst in HFabs0. unfold F_337 in HFabs0. simpl in HFabs0. 
pattern (C u6 u7).
pattern (C u6 u7).
pattern u5.
simpl (memberC _ _). cbv beta. try unfold memberC. try rewrite H. try rewrite H0. try unfold memberC in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 333 ] *)

unfold fst. unfold F_333.
auto.



	(* TOTAL CASE REWRITING on [ 337 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (H: ((nat_eq u6 u6) = true) /\ ((nat_eq u7 u7) = true) \/ ((nat_eq u6 u6) = false) \/ ((nat_eq u6 u6) = true) /\ ((nat_eq u7 u7) = false)). 

destruct ((nat_eq u7 u7)); destruct ((nat_eq u6 u6)); auto.

destruct H as [[H H0]|[H|[H H0]]].

(* rewriting with the axiom [ 82 ] *)

assert (H1 := Hind F_347). clear Hind.
assert (HFabs0 : fst (F_347 u5 u2 u6 u7)).
apply H1. trivial_in 20. unfold snd. unfold F_347. unfold F_337. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_337. unfold F_347. unfold fst in HFabs0. unfold F_347 in HFabs0. simpl in HFabs0. 
pattern u6.
pattern u6.
pattern u7.
pattern u7.
simpl (OBJ_eq _ _). cbv beta. try unfold OBJ_eq. try rewrite H. try rewrite H0. try unfold OBJ_eq in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 83 ] *)

assert (H1 := Hind F_351). clear Hind.
assert (HFabs0 : fst (F_351 u5 u2 u6 u7)).
apply H1. trivial_in 21. unfold snd. unfold F_351. unfold F_337. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_337. unfold F_351. unfold fst in HFabs0. unfold F_351 in HFabs0. simpl in HFabs0. 
pattern u6.
pattern u6.
pattern u7.
pattern u7.
simpl (OBJ_eq _ _). cbv beta. try unfold OBJ_eq. try rewrite H. try rewrite H0. try unfold OBJ_eq in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 84 ] *)

assert (H1 := Hind F_355). clear Hind.
assert (HFabs0 : fst (F_355 u5 u2 u6 u7)).
apply H1. trivial_in 22. unfold snd. unfold F_355. unfold F_337. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_337. unfold F_355. unfold fst in HFabs0. unfold F_355 in HFabs0. simpl in HFabs0. 
pattern u6.
pattern u6.
pattern u7.
pattern u7.
simpl (OBJ_eq _ _). cbv beta. try unfold OBJ_eq. try rewrite H. try rewrite H0. try unfold OBJ_eq in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 347 ] *)

unfold fst. unfold F_347. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 351 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (H := Hind F_356). 
assert (HFabs0 : fst (F_356 u5 u2 u6 u7)).
apply H. trivial_in 23. unfold snd. unfold F_356. unfold F_351. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_351. unfold F_356.

unfold fst in HFabs0. unfold F_356 in HFabs0.
auto.



	(* NEGATIVE DECOMPOSITION on [ 355 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
assert (H := Hind F_357). 
assert (HFabs0 : fst (F_357 u5 u2 u6 u7)).
apply H. trivial_in 24. unfold snd. unfold F_357. unfold F_355. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_355. unfold F_357.

unfold fst in HFabs0. unfold F_357 in HFabs0.
auto.



	(* SUBSUMPTION on [ 356 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
unfold fst. unfold F_356. specialize true_157 with (u1 := u6). intro L. intros. contradict L. (auto || symmetry; auto).



	(* SUBSUMPTION on [ 357 ] *)

rename u1 into _u5. rename u2 into _u2. rename u3 into _u6. rename u4 into _u7. 
rename _u5 into u5. rename _u2 into u2. rename _u6 into u6. rename _u7 into u7. 
unfold fst. unfold F_357. specialize true_157 with (u1 := u7). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_219 := fun f => exists F, In F LF_219 /\ exists e1, exists e2, exists e3, exists e4, f = F e1 e2 e3 e4.

Theorem all_true_219: forall F, In F LF_219 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, fst (F u1 u2  u3  u4).
Proof.
let n := constr:(4) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_219);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_219;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_219: forall (u1: PLAN) (u2: nat), (PLAN_eq (listAt u1 u2) Nil) = false -> (memberC (firstAt u1 u2) u1) = true.
Proof.
do 2 intro.
apply (all_true_219 F_219);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
