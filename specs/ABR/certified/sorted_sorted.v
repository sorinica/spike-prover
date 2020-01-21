
Require Import sorted_sorted_spec.



Definition type_LF_155 :=  PLAN ->  OBJ ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_155 : type_LF_155:= (fun  u2 u1  _ _ _ => ((sortedT (Cons u1 u2)) = true -> (sortedT u2) = true, (Term id_sortedT ((Term id_Cons ((model_OBJ u1):: (model_PLAN u2)::nil))::nil))::(Term id_true nil)::(Term id_sortedT ((model_PLAN u2)::nil))::(Term id_true nil)::nil)).
Definition F_174 : type_LF_155:= (fun  u7  _ u3 u4 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u3 u4) = true -> (sortedT (Cons (C u3 u6) u7)) = true, (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_180 : type_LF_155:= (fun  u7  _ u3 u4 u6 => (false = true -> (le u3 u4) = false -> (sortedT (Cons (C u3 u6) u7)) = true, (Term id_false nil)::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_168 : type_LF_155:= (fun   _  _  _ _ _ => (true = true -> (sortedT Nil) = true, (Term id_true nil)::(Term id_true nil)::(Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_181 : type_LF_155:= (fun   _  _  _ _ _ => ((sortedT Nil) = true, (Term id_sortedT ((Term id_Nil nil)::nil))::(Term id_true nil)::nil)).
Definition F_184 : type_LF_155:= (fun   _  _  _ _ _ => (true = true, (Term id_true nil)::(Term id_true nil)::nil)).

Definition LF_155 := [F_155, F_174, F_180, F_168, F_181, F_184].


Function f_155 (u2: PLAN) (u1: OBJ) {struct u2} : bool :=
 match u2, u1 with
| Nil, _ => true
| (Cons (C u3 u6) u7), (C u4 u5) => true
end.

Lemma main_155 : forall F, In F LF_155 -> forall u1, forall u2, forall u3, forall u4, forall u5, (forall F', In F' LF_155 -> forall e1, forall e2, forall e3, forall e4, forall e5, less (snd (F' e1 e2 e3 e4 e5)) (snd (F u1 u2 u3 u4 u5)) -> fst (F' e1 e2 e3 e4 e5)) -> fst (F u1 u2 u3 u4 u5).
Proof.
intros F HF u1 u2 u3 u4 u5; case_In HF; intro Hind.

	(* GENERATE on [ 155 ] *)

rename u1 into _u2. rename u2 into _u1. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 
rename _u2 into u2. rename _u1 into u1. 

revert Hind.

pattern u2, u1, (f_155 u2 u1). apply f_155_ind.

(* case [ 168 ] *)

intros _u2 _u1.  intro eq_1. intro. intro Heq1. rewrite <- Heq1.  intro HFabs0.
assert (Hind := HFabs0 F_168). clear HFabs0.
assert (HFabs0 : fst (F_168 Nil (C 0 0 ) 0 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_168. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_168.
auto.



intros _u2 _u1. intro u3. intro u6. intro u7.  intro eq_1. intro u4. intro u5.  intro eq_2.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 174 ] *)

assert (Hind := HFabs0 F_174). clear HFabs0.
assert (HFabs0 : fst (F_174 u7 (C 0 0 ) u3 u4 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_174. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_174. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 180 ] *)

assert (Hind := HFabs0 F_180). clear HFabs0.
assert (HFabs0 : fst (F_180 u7 (C 0 0 ) u3 u4 u6)).
apply Hind. trivial_in 2. unfold snd. unfold F_180. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_180. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* TAUTOLOGY on [ 174 ] *)

unfold fst. unfold F_174.
auto.



	(* NEGATIVE CLASH on [ 180 ] *)

unfold fst. unfold F_180. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 168 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (H := Hind F_181). 
assert (HFabs0 : fst (F_181 Nil (C 0 0 ) 0 0 0)).
apply H. trivial_in 4. unfold snd. unfold F_181. unfold F_168. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_168. unfold F_181.

unfold fst in HFabs0. unfold F_181 in HFabs0.
auto.



	(* REWRITING on [ 181 ] *)

rename u1 into d_u1. rename u2 into d_u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. 

assert (Res := Hind F_184). clear Hind.
assert (HFabs1 : fst (F_184 Nil (C 0 0 ) 0 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_184. unfold F_181. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_181. unfold fst in HFabs1. unfold F_184 in HFabs1.    simpl. auto.



	(* TAUTOLOGY on [ 184 ] *)

unfold fst. unfold F_184.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_155 := fun f => exists F, In F LF_155 /\ exists e1, exists e2, exists e3, exists e4, exists e5, f = F e1 e2 e3 e4 e5.

Theorem all_true_155: forall F, In F LF_155 -> forall u1: PLAN, forall u2: OBJ, forall u3: nat, forall u4: nat, forall u5: nat, fst (F u1 u2 u3  u4  u5).
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


Theorem true_155: forall (u2: PLAN) (u1: OBJ), (sortedT (Cons u1 u2)) = true -> (sortedT u2) = true.
Proof.
do 2 intro.
apply (all_true_155 F_155);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
