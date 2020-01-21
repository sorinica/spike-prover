
Require Import null_wind2_spec.



Definition type_LF_156 :=  PLAN ->  OBJ ->  nat ->  nat ->  nat ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_156 : type_LF_156:= (fun  u5 u3 u1 u2 u4 _ _ _ _ => ((le u1 u2) = false -> (le (plus (time u3) u2) u4) = true -> (wind u5 u4 u1 u2) = Nil -> (sortedT (Cons u3 u5)) = true -> u5 = Nil, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_plus ((Term id_time ((model_OBJ u3)::nil)):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_wind ((model_PLAN u5):: (model_nat u4):: (model_nat u1):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_sortedT ((Term id_Cons ((model_OBJ u3):: (model_PLAN u5)::nil))::nil))::(Term id_true nil)::(model_PLAN u5)::(Term id_Nil nil)::nil)).
Definition F_170 : type_LF_156:= (fun   _ u3 u1 u2 u4 _ _ _ _ => ((le u1 u2) = false -> (le (plus (time u3) u2) u4) = true -> (wind Nil u4 u1 u2) = Nil -> true = true -> Nil = Nil, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_plus ((Term id_time ((model_OBJ u3)::nil)):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_wind ((Term id_Nil nil):: (model_nat u4):: (model_nat u1):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_true nil)::(Term id_true nil)::(Term id_Nil nil)::(Term id_Nil nil)::nil)).
Definition F_182 : type_LF_156:= (fun  u10  _ u1 u2 u4 u6 u7 u8 u9 => ((le u1 u2) = false -> (le (plus (time (C u7 u8)) u2) u4) = true -> (wind (Cons (C u6 u9) u10) u4 u1 u2) = Nil -> false = true -> (le u6 u7) = false -> (Cons (C u6 u9) u10) = Nil, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_plus ((Term id_time ((Term id_C ((model_nat u7):: (model_nat u8)::nil))::nil)):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_wind ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil)):: (model_nat u4):: (model_nat u1):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u7)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::(Term id_Nil nil)::nil)).
Definition F_176 : type_LF_156:= (fun  u10  _ u1 u2 u4 u6 u7 u8 u9 => ((le u1 u2) = false -> (le (plus (time (C u7 u8)) u2) u4) = true -> (wind (Cons (C u6 u9) u10) u4 u1 u2) = Nil -> (sortedT (Cons (C u6 u9) u10)) = true -> (le u6 u7) = true -> (Cons (C u6 u9) u10) = Nil, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_plus ((Term id_time ((Term id_C ((model_nat u7):: (model_nat u8)::nil))::nil)):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_wind ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil)):: (model_nat u4):: (model_nat u1):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u7)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::(Term id_Nil nil)::nil)).
Definition F_185 : type_LF_156:= (fun  u10  _ u1 u2 u4 u6 u7 u9 _ => ((le u1 u2) = false -> (le (plus u7 u2) u4) = true -> (wind (Cons (C u6 u9) u10) u4 u1 u2) = Nil -> (sortedT (Cons (C u6 u9) u10)) = true -> (le u6 u7) = true -> (Cons (C u6 u9) u10) = Nil, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_plus ((model_nat u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_wind ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil)):: (model_nat u4):: (model_nat u1):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u7)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::(Term id_Nil nil)::nil)).
Definition F_194 : type_LF_156:= (fun  u10  _ u1 u2 u4 u6 u7 u9 _ => ((le u1 u2) = false -> (le (plus u7 u2) u4) = true -> (Cons (C u6 u9) (wind u10 u4 u1 u2)) = Nil -> (sortedT (Cons (C u6 u9) u10)) = true -> (le u6 u7) = true -> (le (plus u6 u2) u4) = true -> (le (plus u6 u1) u4) = false -> (Cons (C u6 u9) u10) = Nil, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_plus ((model_nat u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (Term id_wind ((model_PLAN u10):: (model_nat u4):: (model_nat u1):: (model_nat u2)::nil))::nil))::(Term id_Nil nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u7)::nil))::(Term id_true nil)::(Term id_le ((Term id_plus ((model_nat u6):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_plus ((model_nat u6):: (model_nat u1)::nil)):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::(Term id_Nil nil)::nil)).
Definition F_202 : type_LF_156:= (fun  u10  _ u1 u2 u4 u6 u7 u9 _ => ((le u1 u2) = false -> (le (plus u7 u2) u4) = true -> (Cons (C u6 u9) Nil) = Nil -> (sortedT (Cons (C u6 u9) u10)) = true -> (le u6 u7) = true -> (le (plus u6 u2) u4) = true -> (le (plus u6 u1) u4) = true -> (Cons (C u6 u9) u10) = Nil, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_plus ((model_nat u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (Term id_Nil nil)::nil))::(Term id_Nil nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u7)::nil))::(Term id_true nil)::(Term id_le ((Term id_plus ((model_nat u6):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_plus ((model_nat u6):: (model_nat u1)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::(Term id_Nil nil)::nil)).
Definition F_198 : type_LF_156:= (fun  u10  _ u1 u2 u4 u6 u7 u9 _ => ((le u1 u2) = false -> (le (plus u7 u2) u4) = true -> (wind u10 u4 u1 u2) = Nil -> (sortedT (Cons (C u6 u9) u10)) = true -> (le u6 u7) = true -> (le (plus u6 u2) u4) = false -> (Cons (C u6 u9) u10) = Nil, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_plus ((model_nat u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_wind ((model_PLAN u10):: (model_nat u4):: (model_nat u1):: (model_nat u2)::nil))::(Term id_Nil nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u6):: (model_nat u7)::nil))::(Term id_true nil)::(Term id_le ((Term id_plus ((model_nat u6):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_Cons ((Term id_C ((model_nat u6):: (model_nat u9)::nil)):: (model_PLAN u10)::nil))::(Term id_Nil nil)::nil)).

Definition LF_156 := [F_156, F_170, F_182, F_176, F_185, F_194, F_202, F_198].


Function f_156 (u5: PLAN) (u3: OBJ) {struct u5} : bool :=
 match u5, u3 with
| Nil, _ => true
| (Cons (C u6 u9) u10), (C u7 u8) => true
end.


Hypothesis true_154: forall u1 u2 u3 u4, (le (plus u1 u2) u3) = true -> (le u4 u1) = true -> (le (plus u4 u2) u3) = false -> False.

Lemma main_156 : forall F, In F LF_156 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, forall u7, forall u8, forall u9, (forall F', In F' LF_156 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, forall e7, forall e8, forall e9, less (snd (F' e1 e2 e3 e4 e5 e6 e7 e8 e9)) (snd (F u1 u2 u3 u4 u5 u6 u7 u8 u9)) -> fst (F' e1 e2 e3 e4 e5 e6 e7 e8 e9)) -> fst (F u1 u2 u3 u4 u5 u6 u7 u8 u9).
Proof.
intros F HF u1 u2 u3 u4 u5 u6 u7 u8 u9; case_In HF; intro Hind.

	(* GENERATE on [ 156 ] *)

rename u1 into _u5. rename u2 into _u3. rename u3 into _u1. rename u4 into _u2. rename u5 into _u4. rename u6 into d_u6. rename u7 into d_u7. rename u8 into d_u8. rename u9 into d_u9. 
rename _u5 into u5. rename _u3 into u3. rename _u1 into u1. rename _u2 into u2. rename _u4 into u4. 

revert Hind.

pattern u5, u3, (f_156 u5 u3). apply f_156_ind.

(* case [ 170 ] *)

intros _u5 _u3.  intro eq_1. intro. intro Heq3. rewrite <- Heq3.  intro HFabs0.
assert (Hind := HFabs0 F_170). clear HFabs0.
assert (HFabs0 : fst (F_170 Nil _u3 u1 u2 u4 0 0 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_170. unfold F_156. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_156. unfold F_170.
auto.



intros _u5 _u3. intro u6. intro u9. intro u10.  intro eq_1. intro u7. intro u8.  intro eq_2.  intro HFabs0.
case_eq (le u6 u7); [intro H | intro H].

(* case [ 176 ] *)

assert (Hind := HFabs0 F_176). clear HFabs0.
assert (HFabs0 : fst (F_176 u10 (C 0 0 ) u1 u2 u4 u6 u7 u8 u9)).
apply Hind. trivial_in 3. unfold snd. unfold F_176. unfold F_156. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_156. unfold F_176. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 182 ] *)

assert (Hind := HFabs0 F_182). clear HFabs0.
assert (HFabs0 : fst (F_182 u10 (C 0 0 ) u1 u2 u4 u6 u7 u8 u9)).
apply Hind. trivial_in 2. unfold snd. unfold F_182. unfold F_156. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_156. unfold F_182. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* TAUTOLOGY on [ 170 ] *)

unfold fst. unfold F_170.
auto.



	(* NEGATIVE CLASH on [ 182 ] *)

unfold fst. unfold F_182. intros. try discriminate.



	(* REWRITING on [ 176 ] *)

rename u1 into _u10. rename u2 into d_u2. rename u3 into _u1. rename u4 into _u2. rename u5 into _u4. rename u6 into _u6. rename u7 into _u7. rename u8 into _u8. rename u9 into _u9. 
rename _u10 into u10. rename _u1 into u1. rename _u2 into u2. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_185). clear Hind.
assert (HFabs1 : fst (F_185 u10 (C 0 0 ) u1 u2 u4 u6 u7 u9 0)).
apply Res. trivial_in 4. unfold snd. unfold F_185. unfold F_176. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_176. unfold fst in HFabs1. unfold F_185 in HFabs1.   
pattern u7, u8. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 185 ] *)

rename u1 into _u10. rename u2 into d_u2. rename u3 into _u1. rename u4 into _u2. rename u5 into _u4. rename u6 into _u6. rename u7 into _u7. rename u8 into _u9. rename u9 into d_u9. 
rename _u10 into u10. rename _u1 into u1. rename _u2 into u2. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. rename _u9 into u9. 
assert (H: ((le (plus u6 u2) u4) = true) /\ ((le (plus u6 u1) u4) = false) \/ ((le (plus u6 u2) u4) = false) \/ ((le (plus u6 u2) u4) = true) /\ ((le (plus u6 u1) u4) = true)). 

destruct ((le (plus u6 u1) u4)); destruct ((le (plus u6 u2) u4)); auto.

destruct H as [[H H0]|[H|[H H0]]].

(* rewriting with the axiom [ 119 ] *)

assert (H1 := Hind F_194). clear Hind.
assert (HFabs0 : fst (F_194 u10 (C 0 0 ) u1 u2 u4 u6 u7 u9 0)).
apply H1. trivial_in 5. unfold snd. unfold F_194. unfold F_185. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_185. unfold F_194. unfold fst in HFabs0. unfold F_194 in HFabs0. simpl in HFabs0. 
pattern u6.
pattern u2.
pattern u4.
pattern u1.
pattern u9.
pattern u10.
simpl (wind _ _ _ _). cbv beta. try unfold wind. try rewrite H. try rewrite H0. try unfold wind in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 120 ] *)

assert (H1 := Hind F_198). clear Hind.
assert (HFabs0 : fst (F_198 u10 (C 0 0 ) u1 u2 u4 u6 u7 u9 0)).
apply H1. trivial_in 7. unfold snd. unfold F_198. unfold F_185. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_185. unfold F_198. unfold fst in HFabs0. unfold F_198 in HFabs0. simpl in HFabs0. 
pattern u6.
pattern u2.
pattern u4.
pattern u9.
pattern u10.
pattern u1.
simpl (wind _ _ _ _). cbv beta. try unfold wind. try rewrite H. try rewrite H0. try unfold wind in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 121 ] *)

assert (H1 := Hind F_202). clear Hind.
assert (HFabs0 : fst (F_202 u10 (C 0 0 ) u1 u2 u4 u6 u7 u9 0)).
apply H1. trivial_in 6. unfold snd. unfold F_202. unfold F_185. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_185. unfold F_202. unfold fst in HFabs0. unfold F_202 in HFabs0. simpl in HFabs0. 
pattern u6.
pattern u2.
pattern u4.
pattern u1.
pattern u9.
pattern u10.
simpl (wind _ _ _ _). cbv beta. try unfold wind. try rewrite H. try rewrite H0. try unfold wind in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* NEGATIVE CLASH on [ 194 ] *)

unfold fst. unfold F_194. intros. try discriminate.



	(* NEGATIVE CLASH on [ 202 ] *)

unfold fst. unfold F_202. intros. try discriminate.



	(* SUBSUMPTION on [ 198 ] *)

rename u1 into _u10. rename u2 into d_u2. rename u3 into _u1. rename u4 into _u2. rename u5 into _u4. rename u6 into _u6. rename u7 into _u7. rename u8 into _u9. rename u9 into d_u9. 
rename _u10 into u10. rename _u1 into u1. rename _u2 into u2. rename _u4 into u4. rename _u6 into u6. rename _u7 into u7. rename _u9 into u9. 
unfold fst. unfold F_198. specialize true_154 with (u1 := u7) (u2 := u2) (u3 := u4) (u4 := u6). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_156 := fun f => exists F, In F LF_156 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, exists e7, exists e8, exists e9, f = F e1 e2 e3 e4 e5 e6 e7 e8 e9.

Theorem all_true_156: forall F, In F LF_156 -> forall u1: PLAN, forall u2: OBJ, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, forall u7: nat, forall u8: nat, forall u9: nat, fst (F u1 u2 u3  u4  u5  u6  u7  u8  u9).
Proof.
let n := constr:(9) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_156);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_156;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_156: forall (u5: PLAN) (u3: OBJ) (u1: nat) (u2: nat) (u4: nat), (le u1 u2) = false -> (le (plus (time u3) u2) u4) = true -> (wind u5 u4 u1 u2) = Nil -> (sortedT (Cons u3 u5)) = true -> u5 = Nil.
Proof.
do 5 intro.
apply (all_true_156 F_156);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
