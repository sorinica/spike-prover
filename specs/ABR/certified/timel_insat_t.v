
Require Import timel_insat_t_spec.



Definition type_LF_155 :=  PLAN ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_155 : type_LF_155:= (fun   u1 u2 u3 _ _ => ((timel (insAt u1 u2 u3)) = u2, (Term id_timel ((Term id_insAt ((model_PLAN u1):: (model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u2)::nil)).
Definition F_167 : type_LF_155:= (fun    _ u2 u3 _ _ => ((timel (Cons (C u2 u3) Nil)) = u2, (Term id_timel ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Nil nil)::nil))::nil))::(model_nat u2)::nil)).
Definition F_173 : type_LF_155:= (fun   u6 u2 u3 u8 u9 => ((le (time (C u8 u9)) u2) = true -> (timel (Cons (C u2 u3) (Cons (C u8 u9) u6))) = u2, (Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timel ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::(model_nat u2)::nil)).
Definition F_179 : type_LF_155:= (fun   u6 u2 u3 u8 u9 => ((le (time (C u8 u9)) u2) = false -> (timel (insAt u6 u2 u3)) = u2, (Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_timel ((Term id_insAt ((model_PLAN u6):: (model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u2)::nil)).
Definition F_182 : type_LF_155:= (fun    _ u2 u3 _ _ => ((time (C u2 u3)) = u2, (Term id_time ((Term id_C ((model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u2)::nil)).
Definition F_193 : type_LF_155:= (fun    _ u2 _ _ _ => (u2 = u2, (model_nat u2)::(model_nat u2)::nil)).
Definition F_185 : type_LF_155:= (fun   u6 u2 u3 u8 u9 => ((le u8 u2) = true -> (timel (Cons (C u2 u3) (Cons (C u8 u9) u6))) = u2, (Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timel ((Term id_Cons ((Term id_C ((model_nat u2):: (model_nat u3)::nil)):: (Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u6)::nil))::nil))::nil))::(model_nat u2)::nil)).
Definition F_190 : type_LF_155:= (fun   u6 u2 u3 u8 _ => ((le u8 u2) = false -> (timel (insAt u6 u2 u3)) = u2, (Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_timel ((Term id_insAt ((model_PLAN u6):: (model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u2)::nil)).
Definition F_202 : type_LF_155:= (fun    _ u2 u8 _ _ => ((le u8 u2) = false -> u2 = u2, (Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(model_nat u2)::(model_nat u2)::nil)).
Definition F_197 : type_LF_155:= (fun    _ u2 u3 u8 _ => ((le u8 u2) = true -> (time (C u2 u3)) = u2, (Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_time ((Term id_C ((model_nat u2):: (model_nat u3)::nil))::nil))::(model_nat u2)::nil)).
Definition F_206 : type_LF_155:= (fun    _ u2 u8 _ _ => ((le u8 u2) = true -> u2 = u2, (Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(model_nat u2)::(model_nat u2)::nil)).

Definition LF_155 := [F_155, F_167, F_173, F_179, F_182, F_193, F_185, F_190, F_202, F_197, F_206].


Function f_155 (u1: PLAN) (u2: nat) (u3: nat) {struct u1} : PLAN :=
 match u1, u2, u3 with
| Nil, _, _ => Nil
| (Cons (C u8 u9) u6), _, _ => Nil
end.

Lemma main_155 : forall F, In F LF_155 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_155 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 155 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. 

revert Hind.

pattern u1, u2, u3, (f_155 u1 u2 u3). apply f_155_ind.

(* case [ 167 ] *)

intros _u1 _u2 _u3.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_167). clear HFabs0.
assert (HFabs0 : fst (F_167 Nil _u2 _u3 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_167. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_167.
auto.



intros _u1 _u2 _u3. intro u8. intro u9. intro u6.  intro eq_1. intro. intro Heq2. rewrite <- Heq2. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
case_eq (le (time (C u8 u9)) _u2); [intro H | intro H].

(* case [ 173 ] *)

assert (Hind := HFabs0 F_173). clear HFabs0.
assert (HFabs0 : fst (F_173 u6 _u2 _u3 u8 u9)).
apply Hind. trivial_in 2. unfold snd. unfold F_173. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_173. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 179 ] *)

assert (Hind := HFabs0 F_179). clear HFabs0.
assert (HFabs0 : fst (F_179 u6 _u2 _u3 u8 u9)).
apply Hind. trivial_in 3. unfold snd. unfold F_179. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_179. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* REWRITING on [ 167 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_182). clear Hind.
assert (HFabs1 : fst (F_182 Nil u2 u3 0 0)).
apply Res. trivial_in 4. unfold snd. unfold F_182. unfold F_167. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_167. unfold fst in HFabs1. unfold F_182 in HFabs1.   
pattern (C u2 u3), Nil. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 173 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_185). clear Hind.
assert (HFabs1 : fst (F_185 u6 u2 u3 u8 u9)).
apply Res. trivial_in 6. unfold snd. unfold F_185. unfold F_173. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_173. unfold fst in HFabs1. unfold F_185 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 179 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_190). clear Hind.
assert (HFabs1 : fst (F_190 u6 u2 u3 u8 0)).
apply Res. trivial_in 7. unfold snd. unfold F_190. unfold F_179. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_179. unfold fst in HFabs1. unfold F_190 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 182 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u3 into u3. 
assert (Res := Hind F_193). clear Hind.
assert (HFabs1 : fst (F_193 Nil u2 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_193. unfold F_182. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_182. unfold fst in HFabs1. unfold F_193 in HFabs1.   
pattern u2, u3. simpl (time _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 193 ] *)

unfold fst. unfold F_193.
auto.



	(* REWRITING on [ 185 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into _u9. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_197). clear Hind.
assert (HFabs1 : fst (F_197 Nil u2 u3 u8 0)).
apply Res. trivial_in 9. unfold snd. unfold F_197. unfold F_185. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_185. unfold fst in HFabs1. unfold F_197 in HFabs1.   
pattern (C u2 u3), (Cons (C u8 u9) u6). simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 190 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into d_u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. 
assert (H := Hind F_155).
assert (Res := Hind F_202). clear Hind.
assert (HFabs0 : fst (F_155 u6 u2 u3 0 0)).
apply H. trivial_in 0. unfold snd. unfold F_155. unfold F_190. rewrite_model. abstract solve_rpo_mul.
unfold fst in HFabs0. unfold F_155 in HFabs0. simpl in HFabs0.

assert (HFabs1 : fst (F_202 Nil u2 u8 0 0)).
apply Res. trivial_in 8. unfold snd. unfold F_202. unfold F_190. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_190. unfold fst in HFabs1. unfold F_202 in HFabs1.   
pattern u6, u2, u3. simpl (timel _). cbv beta.
try rewrite  HFabs0.  simpl. auto.



	(* TAUTOLOGY on [ 202 ] *)

unfold fst. unfold F_202.
auto.



	(* REWRITING on [ 197 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u8. rename u5 into d_u5. 
rename _u2 into u2. rename _u3 into u3. rename _u8 into u8. 
assert (Res := Hind F_206). clear Hind.
assert (HFabs1 : fst (F_206 Nil u2 u8 0 0)).
apply Res. trivial_in 10. unfold snd. unfold F_206. unfold F_197. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_197. unfold fst in HFabs1. unfold F_206 in HFabs1.   
pattern u2, u3. simpl (time _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 206 ] *)

unfold fst. unfold F_206.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_155 := fun f => exists F, In F LF_155 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_155: forall F, In F LF_155 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2  u3  u4  u5).
Proof.
let n := constr:(5) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_155);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_155;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_155: forall (u1: PLAN) (u2: nat) (u3: nat), (timel (insAt u1 u2 u3)) = u2.
Proof.
do 3 intro.
apply (all_true_155 F_155);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
