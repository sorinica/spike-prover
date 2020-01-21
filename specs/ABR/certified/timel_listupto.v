
Require Import timel_listupto_spec.



Definition type_LF_155 :=  PLAN ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_155 : type_LF_155:= (fun   u1 u2 _ _ => ((timel (listUpTo u1 u2)) = (timel u1), (Term id_timel ((Term id_listUpTo ((model_PLAN u1):: (model_nat u2)::nil))::nil))::(Term id_timel ((model_PLAN u1)::nil))::nil)).
Definition F_167 : type_LF_155:= (fun    _  _ _ _ => ((timel Nil) = (timel Nil), (Term id_timel ((Term id_Nil nil)::nil))::(Term id_timel ((Term id_Nil nil)::nil))::nil)).
Definition F_173 : type_LF_155:= (fun   u6 u2 u3 u5 => ((le u3 u2) = true -> (timel (Cons (C u3 u5) Nil)) = (timel (Cons (C u3 u5) u6)), (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil))::(Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::nil)).
Definition F_179 : type_LF_155:= (fun   u6 u2 u3 u5 => ((le u3 u2) = false -> (timel (Cons (C u3 u5) (listUpTo u6 u2))) = (timel (Cons (C u3 u5) u6)), (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (Term id_listUpTo ((model_PLAN u6):: (model_nat u2)::nil))::nil))::nil))::(Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::nil)).
Definition F_182 : type_LF_155:= (fun   u6 u2 u3 u5 => ((le u3 u2) = true -> (time (C u3 u5)) = (timel (Cons (C u3 u5) u6)), (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_time ((Term id_C ((model_nat u3):: (model_nat u5)::nil))::nil))::(Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::nil)).
Definition F_188 : type_LF_155:= (fun    _ u2 u3 u5 => ((le u3 u2) = true -> (time (C u3 u5)) = (time (C u3 u5)), (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_time ((Term id_C ((model_nat u3):: (model_nat u5)::nil))::nil))::(Term id_time ((Term id_C ((model_nat u3):: (model_nat u5)::nil))::nil))::nil)).
Definition F_185 : type_LF_155:= (fun   u6 u2 u3 u5 => ((le u3 u2) = false -> (time (C u3 u5)) = (timel (Cons (C u3 u5) u6)), (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_time ((Term id_C ((model_nat u3):: (model_nat u5)::nil))::nil))::(Term id_timel ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u5)::nil)):: (model_PLAN u6)::nil))::nil))::nil)).
Definition F_191 : type_LF_155:= (fun    _ u2 u3 u5 => ((le u3 u2) = false -> (time (C u3 u5)) = (time (C u3 u5)), (Term id_le ((model_nat u3):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_time ((Term id_C ((model_nat u3):: (model_nat u5)::nil))::nil))::(Term id_time ((Term id_C ((model_nat u3):: (model_nat u5)::nil))::nil))::nil)).

Definition LF_155 := [F_155, F_167, F_173, F_179, F_182, F_188, F_185, F_191].


Function f_155 (u1: PLAN) (u2: nat) {struct u1} : PLAN :=
 match u1, u2 with
| Nil, _ => Nil
| (Cons (C u3 u5) u6), _ => Nil
end.

Lemma main_155 : forall F, In F LF_155 -> forall u1, forall u2, forall u3, forall u4, (forall F', In F' LF_155 -> forall e1, forall e2, forall e3, forall e4, less (snd (F' e1 e2 e3 e4)) (snd (F u1 u2 u3 u4)) -> fst (F' e1 e2 e3 e4)) -> fst (F u1 u2 u3 u4).
Proof.
intros F HF u1 u2 u3 u4; case_In HF; intro Hind.

	(* GENERATE on [ 155 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_155 u1 u2). apply f_155_ind.

(* case [ 167 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_167). clear HFabs0.
assert (HFabs0 : fst (F_167 Nil 0 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_167. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_167.
auto.



intros _u1 _u2. intro u3. intro u5. intro u6.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
case_eq (le u3 _u2); [intro H | intro H].

(* case [ 173 ] *)

assert (Hind := HFabs0 F_173). clear HFabs0.
assert (HFabs0 : fst (F_173 u6 _u2 u3 u5)).
apply Hind. trivial_in 2. unfold snd. unfold F_173. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_173. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 179 ] *)

assert (Hind := HFabs0 F_179). clear HFabs0.
assert (HFabs0 : fst (F_179 u6 _u2 u3 u5)).
apply Hind. trivial_in 3. unfold snd. unfold F_179. unfold F_155. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_155. unfold F_179. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* TAUTOLOGY on [ 167 ] *)

unfold fst. unfold F_167.
auto.



	(* REWRITING on [ 173 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_182). clear Hind.
assert (HFabs1 : fst (F_182 u6 u2 u3 u5)).
apply Res. trivial_in 4. unfold snd. unfold F_182. unfold F_173. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_173. unfold fst in HFabs1. unfold F_182 in HFabs1.   
pattern (C u3 u5), Nil. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 179 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_185). clear Hind.
assert (HFabs1 : fst (F_185 u6 u2 u3 u5)).
apply Res. trivial_in 6. unfold snd. unfold F_185. unfold F_179. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_179. unfold fst in HFabs1. unfold F_185 in HFabs1.   
pattern (C u3 u5), (listUpTo u6 u2). simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 182 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_188). clear Hind.
assert (HFabs1 : fst (F_188 Nil u2 u3 u5)).
apply Res. trivial_in 5. unfold snd. unfold F_188. unfold F_182. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_182. unfold fst in HFabs1. unfold F_188 in HFabs1.   
pattern (C u3 u5), u6. simpl (timel _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 188 ] *)

unfold fst. unfold F_188.
auto.



	(* REWRITING on [ 185 ] *)

rename u1 into _u6. rename u2 into _u2. rename u3 into _u3. rename u4 into _u5. 
rename _u6 into u6. rename _u2 into u2. rename _u3 into u3. rename _u5 into u5. 
assert (Res := Hind F_191). clear Hind.
assert (HFabs1 : fst (F_191 Nil u2 u3 u5)).
apply Res. trivial_in 7. unfold snd. unfold F_191. unfold F_185. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_185. unfold fst in HFabs1. unfold F_191 in HFabs1.   
pattern (C u3 u5), u6. simpl (timel _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 191 ] *)

unfold fst. unfold F_191.
auto.



Qed.



(* the set of all formula instances from the proof *)
Definition S_155 := fun f => exists F, In F LF_155 /\ exists e1, exists e2, exists e3, exists e4, f = F e1 e2 e3 e4.

Theorem all_true_155: forall F, In F LF_155 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, fst (F u1 u2  u3  u4).
Proof.
let n := constr:(4) in
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


Theorem true_155: forall (u1: PLAN) (u2: nat), (timel (listUpTo u1 u2)) = (timel u1).
Proof.
do 2 intro.
apply (all_true_155 F_155);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
