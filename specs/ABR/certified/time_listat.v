
Require Import time_listat_spec.



Definition type_LF_156 :=  nat ->  nat -> (Prop * (List.list term)).

Definition F_156 : type_LF_156:= (fun    u1 u2 => ((le u1 u2) = false -> (le u1 u2) = true -> False, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_171 : type_LF_156:= (fun    u2 _ => (true = false -> (le 0 u2) = true -> False, (Term id_true nil)::(Term id_false nil)::(Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_177 : type_LF_156:= (fun    u3 _ => (false = false -> (le (S u3) 0) = true -> False, (Term id_false nil)::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_183 : type_LF_156:= (fun    u3 u4 => ((le u3 u4) = false -> (le (S u3) (S u4)) = true -> False, (Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_S ((model_nat u4)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_184 : type_LF_156:= (fun    u3 _ => ((le (S u3) 0) = true -> False, (Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_190 : type_LF_156:= (fun     _ _ => (false = true -> False, (Term id_false nil)::(Term id_true nil)::nil)).

Definition LF_156 := [F_156, F_171, F_177, F_183, F_184, F_190].


Function f_156 (u1: nat) (u2: nat) {struct u1} : bool :=
 match u1, u2 with
| 0, _ => true
| (S u3), 0 => true
| (S u3), (S u4) => true
end.

Lemma main_156 : forall F, In F LF_156 -> forall u1, forall u2, (forall F', In F' LF_156 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 156 ] *)

rename u1 into _u1. rename u2 into _u2. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_156 u1 u2). apply f_156_ind.

(* case [ 171 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_171). clear HFabs0.
assert (HFabs0 : fst (F_171 _u2 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_171. unfold F_156. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_156. unfold F_171.
auto.


(* case [ 177 ] *)

intros _u1 _u2. intro u3.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_177). clear HFabs0.
assert (HFabs0 : fst (F_177 u3 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_177. unfold F_156. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_156. unfold F_177.
auto.


(* case [ 183 ] *)

intros _u1 _u2. intro u3.  intro eq_1. intro u4.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_183). clear HFabs0.
assert (HFabs0 : fst (F_183 u3 u4)).
apply Hind. trivial_in 3. unfold snd. unfold F_183. unfold F_156. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_156. unfold F_183.
auto.





	(* NEGATIVE CLASH on [ 171 ] *)

unfold fst. unfold F_171. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 177 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (H := Hind F_184). 
assert (HFabs0 : fst (F_184 u3 0)).
apply H. trivial_in 4. unfold snd. unfold F_184. unfold F_177. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_177. unfold F_184.

unfold fst in HFabs0. unfold F_184 in HFabs0.
auto.



	(* REWRITING on [ 183 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_156). clear Hind.
assert (HFabs1 : fst (F_156 u3 u4)).
apply Res. trivial_in 0. unfold snd. unfold F_156. unfold F_183. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_183. unfold fst in HFabs1. unfold F_156 in HFabs1.   
pattern u3, u4. simpl (le _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 184 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (Res := Hind F_190). clear Hind.
assert (HFabs1 : fst (F_190 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_190. unfold F_184. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_184. unfold fst in HFabs1. unfold F_190 in HFabs1.   
pattern u3. simpl (le _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE CLASH on [ 190 ] *)

unfold fst. unfold F_190. intros. try discriminate.



Qed.



(* the set of all formula instances from the proof *)
Definition S_156 := fun f => exists F, In F LF_156 /\ exists e1, exists e2, f = F e1 e2.

Theorem all_true_156: forall F, In F LF_156 -> forall u1: nat, forall u2: nat, fst (F u1  u2).
Proof.
let n := constr:(2) in
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


Theorem true_156: forall (u1: nat) (u2: nat), (le u1 u2) = false -> (le u1 u2) = true -> False.
Proof.
do 2 intro.
apply (all_true_156 F_156);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_194 :=  PLAN ->  nat ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_194 : type_LF_194:= (fun   u1 u2 _ _ _ _ => ((sortedT u1) = true -> (le (timel u1) u2) = true -> (listAt u1 u2) = u1, (Term id_sortedT ((model_PLAN u1)::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((model_PLAN u1)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((model_PLAN u1):: (model_nat u2)::nil))::(model_PLAN u1)::nil)).
Definition F_227 : type_LF_194:= (fun   u7 u2 u3 u4 u5 u6 => (false = true -> (le (timel (Cons (C u4 u5) (Cons (C u3 u6) u7))) u2) = true -> (le u3 u4) = false -> (listAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) = (Cons (C u4 u5) (Cons (C u3 u6) u7)), (Term id_false nil)::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil)).
Definition F_209 : type_LF_194:= (fun    _ u2 _ _ _ _ => (true = true -> (le (timel Nil) u2) = true -> (listAt Nil u2) = Nil, (Term id_true nil)::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_Nil nil)::nil)).
Definition F_215 : type_LF_194:= (fun    _ u2 u4 u5 _ _ => (true = true -> (le (timel (Cons (C u4 u5) Nil)) u2) = true -> (listAt (Cons (C u4 u5) Nil) u2) = (Cons (C u4 u5) Nil), (Term id_true nil)::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)).
Definition F_221 : type_LF_194:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le (timel (Cons (C u4 u5) (Cons (C u3 u6) u7))) u2) = true -> (le u3 u4) = true -> (listAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) = (Cons (C u4 u5) (Cons (C u3 u6) u7)), (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil)).
Definition F_228 : type_LF_194:= (fun    _ u2 _ _ _ _ => ((le (timel Nil) u2) = true -> (listAt Nil u2) = Nil, (Term id_le ((Term id_timel ((Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_Nil nil)::nil)).
Definition F_229 : type_LF_194:= (fun    _ u2 u4 u5 _ _ => ((le (timel (Cons (C u4 u5) Nil)) u2) = true -> (listAt (Cons (C u4 u5) Nil) u2) = (Cons (C u4 u5) Nil), (Term id_le ((Term id_timel ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)).
Definition F_232 : type_LF_194:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le (time (C u4 u5)) u2) = true -> (le u3 u4) = true -> (listAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) = (Cons (C u4 u5) (Cons (C u3 u6) u7)), (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil)).
Definition F_235 : type_LF_194:= (fun    _ u2 _ _ _ _ => ((le 0 u2) = true -> (listAt Nil u2) = Nil, (Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_Nil nil)::nil)).
Definition F_244 : type_LF_194:= (fun    _ u2 _ _ _ _ => ((le 0 u2) = true -> Nil = Nil, (Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_Nil nil)::(Term id_Nil nil)::nil)).
Definition F_238 : type_LF_194:= (fun    _ u2 u4 u5 _ _ => ((le (time (C u4 u5)) u2) = true -> (listAt (Cons (C u4 u5) Nil) u2) = (Cons (C u4 u5) Nil), (Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)).
Definition F_241 : type_LF_194:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u4 u2) = true -> (le u3 u4) = true -> (listAt (Cons (C u4 u5) (Cons (C u3 u6) u7)) u2) = (Cons (C u4 u5) (Cons (C u3 u6) u7)), (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil)):: (model_nat u2)::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil)).
Definition F_259 : type_LF_194:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u4 u2) = true -> (le u3 u4) = true -> (le (time (C u4 u5)) u2) = true -> (Cons (C u4 u5) (Cons (C u3 u6) u7)) = (Cons (C u4 u5) (Cons (C u3 u6) u7)), (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil)).
Definition F_263 : type_LF_194:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u4 u2) = true -> (le u3 u4) = true -> (le (time (C u4 u5)) u2) = false -> (listAt (Cons (C u3 u6) u7) u2) = (Cons (C u4 u5) (Cons (C u3 u6) u7)), (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil)).
Definition F_266 : type_LF_194:= (fun   u7 u2 u3 u4 u5 u6 => ((sortedT (Cons (C u3 u6) u7)) = true -> (le u4 u2) = true -> (le u3 u4) = true -> (le u4 u2) = false -> (listAt (Cons (C u3 u6) u7) u2) = (Cons (C u4 u5) (Cons (C u3 u6) u7)), (Term id_sortedT ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Cons ((Term id_C ((model_nat u3):: (model_nat u6)::nil)):: (model_PLAN u7)::nil))::nil))::nil)).
Definition F_247 : type_LF_194:= (fun    _ u2 u4 u5 _ _ => ((le u4 u2) = true -> (listAt (Cons (C u4 u5) Nil) u2) = (Cons (C u4 u5) Nil), (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_listAt ((Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil)):: (model_nat u2)::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)).
Definition F_274 : type_LF_194:= (fun    _ u2 u4 u5 _ _ => ((le u4 u2) = true -> (le (time (C u4 u5)) u2) = true -> (Cons (C u4 u5) Nil) = (Cons (C u4 u5) Nil), (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)).
Definition F_278 : type_LF_194:= (fun    _ u2 u4 u5 _ _ => ((le u4 u2) = true -> (le (time (C u4 u5)) u2) = false -> (listAt Nil u2) = (Cons (C u4 u5) Nil), (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_listAt ((Term id_Nil nil):: (model_nat u2)::nil))::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)).
Definition F_281 : type_LF_194:= (fun    _ u2 u4 u5 _ _ => ((le u4 u2) = true -> (le (time (C u4 u5)) u2) = false -> Nil = (Cons (C u4 u5) Nil), (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u4):: (model_nat u5)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_Nil nil)::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)).
Definition F_284 : type_LF_194:= (fun    _ u2 u4 u5 _ _ => ((le u4 u2) = true -> (le u4 u2) = false -> Nil = (Cons (C u4 u5) Nil), (Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_Nil nil)::(Term id_Cons ((Term id_C ((model_nat u4):: (model_nat u5)::nil)):: (Term id_Nil nil)::nil))::nil)).

Definition LF_194 := [F_194, F_227, F_209, F_215, F_221, F_228, F_229, F_232, F_235, F_244, F_238, F_241, F_259, F_263, F_266, F_247, F_274, F_278, F_281, F_284].


Function f_194 (u1: PLAN) {struct u1} : bool :=
 match u1 with
| Nil => true
| (Cons (C u4 u5) Nil) => true
| (Cons (C u4 u5) (Cons (C u3 u6) u7)) => true
end.

Lemma main_194 : forall F, In F LF_194 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, (forall F', In F' LF_194 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, less (snd (F' e1 e2 e3 e4 e5 e6)) (snd (F u1 u2 u3 u4 u5 u6)) -> fst (F' e1 e2 e3 e4 e5 e6)) -> fst (F u1 u2 u3 u4 u5 u6).
Proof.
intros F HF u1 u2 u3 u4 u5 u6; case_In HF; intro Hind.

	(* GENERATE on [ 194 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, (f_194 u1). apply f_194_ind.

(* case [ 209 ] *)

intros _u1.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_209). clear HFabs0.
assert (HFabs0 : fst (F_209 Nil u2 0 0 0 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_209. unfold F_194. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_194. unfold F_209.
auto.


(* case [ 215 ] *)

intros _u1. intro u4. intro u5.  intro eq_1.  intro HFabs0.
assert (Hind := HFabs0 F_215). clear HFabs0.
assert (HFabs0 : fst (F_215 Nil u2 u4 u5 0 0)).
apply Hind. trivial_in 3. unfold snd. unfold F_215. unfold F_194. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_194. unfold F_215.
auto.



intros _u1. intro u4. intro u5. intro u3. intro u6. intro u7.  intro eq_1.  intro HFabs0.
case_eq (le u3 u4); [intro H | intro H].

(* case [ 221 ] *)

assert (Hind := HFabs0 F_221). clear HFabs0.
assert (HFabs0 : fst (F_221 u7 u2 u3 u4 u5 u6)).
apply Hind. trivial_in 4. unfold snd. unfold F_221. unfold F_194. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_194. unfold F_221. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 227 ] *)

assert (Hind := HFabs0 F_227). clear HFabs0.
assert (HFabs0 : fst (F_227 u7 u2 u3 u4 u5 u6)).
apply Hind. trivial_in 1. unfold snd. unfold F_227. unfold F_194. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_194. unfold F_227. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* NEGATIVE CLASH on [ 227 ] *)

unfold fst. unfold F_227. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 209 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. 
assert (H := Hind F_228). 
assert (HFabs0 : fst (F_228 Nil u2 0 0 0 0)).
apply H. trivial_in 5. unfold snd. unfold F_228. unfold F_209. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_209. unfold F_228.

unfold fst in HFabs0. unfold F_228 in HFabs0.
auto.



	(* NEGATIVE DECOMPOSITION on [ 215 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (H := Hind F_229). 
assert (HFabs0 : fst (F_229 Nil u2 u4 u5 0 0)).
apply H. trivial_in 6. unfold snd. unfold F_229. unfold F_215. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_215. unfold F_229.

unfold fst in HFabs0. unfold F_229 in HFabs0.
auto.



	(* REWRITING on [ 221 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_232). clear Hind.
assert (HFabs1 : fst (F_232 u7 u2 u3 u4 u5 u6)).
apply Res. trivial_in 7. unfold snd. unfold F_232. unfold F_221. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_221. unfold fst in HFabs1. unfold F_232 in HFabs1.   
pattern (C u4 u5), (Cons (C u3 u6) u7). simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 228 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. 
assert (Res := Hind F_235). clear Hind.
assert (HFabs1 : fst (F_235 Nil u2 0 0 0 0)).
apply Res. trivial_in 8. unfold snd. unfold F_235. unfold F_228. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_228. unfold fst in HFabs1. unfold F_235 in HFabs1.    simpl. auto.



	(* REWRITING on [ 229 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_238). clear Hind.
assert (HFabs1 : fst (F_238 Nil u2 u4 u5 0 0)).
apply Res. trivial_in 10. unfold snd. unfold F_238. unfold F_229. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_229. unfold fst in HFabs1. unfold F_238 in HFabs1.   
pattern (C u4 u5), Nil. simpl (timel _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 232 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_241). clear Hind.
assert (HFabs1 : fst (F_241 u7 u2 u3 u4 u5 u6)).
apply Res. trivial_in 11. unfold snd. unfold F_241. unfold F_232. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_232. unfold fst in HFabs1. unfold F_241 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 235 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into d_u3. rename u4 into d_u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. 
assert (Res := Hind F_244). clear Hind.
assert (HFabs1 : fst (F_244 Nil u2 0 0 0 0)).
apply Res. trivial_in 9. unfold snd. unfold F_244. unfold F_235. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_235. unfold fst in HFabs1. unfold F_244 in HFabs1.   
pattern u2. simpl (listAt _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 244 ] *)

unfold fst. unfold F_244.
auto.



	(* REWRITING on [ 238 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_247). clear Hind.
assert (HFabs1 : fst (F_247 Nil u2 u4 u5 0 0)).
apply Res. trivial_in 15. unfold snd. unfold F_247. unfold F_238. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_238. unfold fst in HFabs1. unfold F_247 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 241 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (H: ((le (time (C u4 u5)) u2) = true) \/ ((le (time (C u4 u5)) u2) = false)). 

destruct ((le (time (C u4 u5)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 146 ] *)

assert (H1 := Hind F_259). clear Hind.
assert (HFabs0 : fst (F_259 u7 u2 u3 u4 u5 u6)).
apply H1. trivial_in 12. unfold snd. unfold F_259. unfold F_241. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_241. unfold F_259. unfold fst in HFabs0. unfold F_259 in HFabs0. simpl in HFabs0. 
pattern (C u4 u5).
pattern u2.
pattern (Cons (C u3 u6) u7).
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 147 ] *)

assert (H1 := Hind F_263). clear Hind.
assert (HFabs0 : fst (F_263 u7 u2 u3 u4 u5 u6)).
apply H1. trivial_in 13. unfold snd. unfold F_263. unfold F_241. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_241. unfold F_263. unfold fst in HFabs0. unfold F_263 in HFabs0. simpl in HFabs0. 
pattern (C u4 u5).
pattern u2.
pattern (Cons (C u3 u6) u7).
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 259 ] *)

unfold fst. unfold F_259.
auto.



	(* REWRITING on [ 263 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
assert (Res := Hind F_266). clear Hind.
assert (HFabs1 : fst (F_266 u7 u2 u3 u4 u5 u6)).
apply Res. trivial_in 14. unfold snd. unfold F_266. unfold F_263. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_263. unfold fst in HFabs1. unfold F_266 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 266 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u5. rename u6 into _u6. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u5 into u5. rename _u6 into u6. 
unfold fst. unfold F_266. specialize true_156 with (u1 := u4) (u2 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 247 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (H: ((le (time (C u4 u5)) u2) = true) \/ ((le (time (C u4 u5)) u2) = false)). 

destruct ((le (time (C u4 u5)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 146 ] *)

assert (H1 := Hind F_274). clear Hind.
assert (HFabs0 : fst (F_274 Nil u2 u4 u5 0 0)).
apply H1. trivial_in 16. unfold snd. unfold F_274. unfold F_247. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_247. unfold F_274. unfold fst in HFabs0. unfold F_274 in HFabs0. simpl in HFabs0. 
pattern (C u4 u5).
pattern u2.
pattern Nil.
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 147 ] *)

assert (H1 := Hind F_278). clear Hind.
assert (HFabs0 : fst (F_278 Nil u2 u4 u5 0 0)).
apply H1. trivial_in 17. unfold snd. unfold F_278. unfold F_247. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_247. unfold F_278. unfold fst in HFabs0. unfold F_278 in HFabs0. simpl in HFabs0. 
pattern (C u4 u5).
pattern u2.
pattern Nil.
simpl (listAt _ _). cbv beta. try unfold listAt. try rewrite H. try rewrite H0. try unfold listAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* TAUTOLOGY on [ 274 ] *)

unfold fst. unfold F_274.
auto.



	(* REWRITING on [ 278 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_281). clear Hind.
assert (HFabs1 : fst (F_281 Nil u2 u4 u5 0 0)).
apply Res. trivial_in 18. unfold snd. unfold F_281. unfold F_278. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_278. unfold fst in HFabs1. unfold F_281 in HFabs1.   
pattern u2. simpl (listAt _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 281 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
assert (Res := Hind F_284). clear Hind.
assert (HFabs1 : fst (F_284 Nil u2 u4 u5 0 0)).
apply Res. trivial_in 19. unfold snd. unfold F_284. unfold F_281. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_281. unfold fst in HFabs1. unfold F_284 in HFabs1.   
pattern u4, u5. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 284 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u4. rename u4 into _u5. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u4 into u4. rename _u5 into u5. 
unfold fst. unfold F_284. specialize true_156 with (u1 := u4) (u2 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_194 := fun f => exists F, In F LF_194 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, f = F e1 e2 e3 e4 e5 e6.

Theorem all_true_194: forall F, In F LF_194 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, fst (F u1 u2  u3  u4  u5  u6).
Proof.
let n := constr:(6) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_194);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_194;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_194: forall (u1: PLAN) (u2: nat), (sortedT u1) = true -> (le (timel u1) u2) = true -> (listAt u1 u2) = u1.
Proof.
do 2 intro.
apply (all_true_194 F_194);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
