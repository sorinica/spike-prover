
Require Import no_time_spec.



Definition type_LF_157 :=  nat ->  nat -> (Prop * (List.list term)).

Definition F_157 : type_LF_157:= (fun    u1 u2 => ((le u1 u2) = false -> (le u1 u2) = true -> False, (Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u1):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_172 : type_LF_157:= (fun    u2 _ => (true = false -> (le 0 u2) = true -> False, (Term id_true nil)::(Term id_false nil)::(Term id_le ((Term id_0 nil):: (model_nat u2)::nil))::(Term id_true nil)::nil)).
Definition F_178 : type_LF_157:= (fun    u3 _ => (false = false -> (le (S u3) 0) = true -> False, (Term id_false nil)::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_184 : type_LF_157:= (fun    u3 u4 => ((le u3 u4) = false -> (le (S u3) (S u4)) = true -> False, (Term id_le ((model_nat u3):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_S ((model_nat u4)::nil))::nil))::(Term id_true nil)::nil)).
Definition F_185 : type_LF_157:= (fun    u3 _ => ((le (S u3) 0) = true -> False, (Term id_le ((Term id_S ((model_nat u3)::nil)):: (Term id_0 nil)::nil))::(Term id_true nil)::nil)).
Definition F_191 : type_LF_157:= (fun     _ _ => (false = true -> False, (Term id_false nil)::(Term id_true nil)::nil)).

Definition LF_157 := [F_157, F_172, F_178, F_184, F_185, F_191].


Function f_157 (u1: nat) (u2: nat) {struct u1} : bool :=
 match u1, u2 with
| 0, _ => true
| (S u3), 0 => true
| (S u3), (S u4) => true
end.

Lemma main_157 : forall F, In F LF_157 -> forall u1, forall u2, (forall F', In F' LF_157 -> forall e1, forall e2, less (snd (F' e1 e2)) (snd (F u1 u2)) -> fst (F' e1 e2)) -> fst (F u1 u2).
Proof.
intros F HF u1 u2; case_In HF; intro Hind.

	(* GENERATE on [ 157 ] *)

rename u1 into _u1. rename u2 into _u2. 
rename _u1 into u1. rename _u2 into u2. 

revert Hind.

pattern u1, u2, (f_157 u1 u2). apply f_157_ind.

(* case [ 172 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_172). clear HFabs0.
assert (HFabs0 : fst (F_172 _u2 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_172. unfold F_157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_157. unfold F_172.
auto.


(* case [ 178 ] *)

intros _u1 _u2. intro u3.  intro eq_1.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_178). clear HFabs0.
assert (HFabs0 : fst (F_178 u3 0)).
apply Hind. trivial_in 2. unfold snd. unfold F_178. unfold F_157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_157. unfold F_178.
auto.


(* case [ 184 ] *)

intros _u1 _u2. intro u3.  intro eq_1. intro u4.  intro eq_2.  intro HFabs0.
assert (Hind := HFabs0 F_184). clear HFabs0.
assert (HFabs0 : fst (F_184 u3 u4)).
apply Hind. trivial_in 3. unfold snd. unfold F_184. unfold F_157. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_157. unfold F_184.
auto.





	(* NEGATIVE CLASH on [ 172 ] *)

unfold fst. unfold F_172. intros. try discriminate.



	(* NEGATIVE DECOMPOSITION on [ 178 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (H := Hind F_185). 
assert (HFabs0 : fst (F_185 u3 0)).
apply H. trivial_in 4. unfold snd. unfold F_185. unfold F_178. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_178. unfold F_185.

unfold fst in HFabs0. unfold F_185 in HFabs0.
auto.



	(* REWRITING on [ 184 ] *)

rename u1 into _u3. rename u2 into _u4. 
rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_157). clear Hind.
assert (HFabs1 : fst (F_157 u3 u4)).
apply Res. trivial_in 0. unfold snd. unfold F_157. unfold F_184. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_184. unfold fst in HFabs1. unfold F_157 in HFabs1.   
pattern u3, u4. simpl (le _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 185 ] *)

rename u1 into _u3. rename u2 into d_u2. 
rename _u3 into u3. 
assert (Res := Hind F_191). clear Hind.
assert (HFabs1 : fst (F_191 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_191. unfold F_185. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_185. unfold fst in HFabs1. unfold F_191 in HFabs1.   
pattern u3. simpl (le _ _). cbv beta.
 simpl. auto.



	(* NEGATIVE CLASH on [ 191 ] *)

unfold fst. unfold F_191. intros. try discriminate.



Qed.



(* the set of all formula instances from the proof *)
Definition S_157 := fun f => exists F, In F LF_157 /\ exists e1, exists e2, f = F e1 e2.

Theorem all_true_157: forall F, In F LF_157 -> forall u1: nat, forall u2: nat, fst (F u1  u2).
Proof.
let n := constr:(2) in
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


Theorem true_157: forall (u1: nat) (u2: nat), (le u1 u2) = false -> (le u1 u2) = true -> False.
Proof.
do 2 intro.
apply (all_true_157 F_157);
 (trivial_in 0) ||
 (repeat constructor).
Qed.


Definition type_LF_195 :=  PLAN ->  nat ->  nat ->  nat ->  nat ->  nat -> (Prop * (List.list term)).

Definition F_195 : type_LF_195:= (fun   u1 u2 u3 u4 _ _ => ((progAt u1 u2) = u3 -> (le u4 u2) = true -> (le (timeAt u1 u2) u4) = true -> (progAt u1 u4) = u3, (Term id_progAt ((model_PLAN u1):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u1):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_progAt ((model_PLAN u1):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_209 : type_LF_195:= (fun    _ u2 u3 u4 _ _ => ((progAt Nil u2) = u3 -> (le u4 u2) = true -> (le 0 u4) = true -> (progAt Nil u4) = u3, (Term id_progAt ((Term id_Nil nil):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_0 nil):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Nil nil):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_215 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le (time (C u8 u9)) u4) = true -> (le (time (C u8 u9)) u2) = true -> (progAt (Cons (C u8 u9) u7) u4) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_221 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le (timeAt u7 u2) u4) = true -> (le (time (C u8 u9)) u2) = false -> (progAt (Cons (C u8 u9) u7) u4) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_224 : type_LF_195:= (fun    _ u2 u3 u4 _ _ => ((progAt Nil u2) = u3 -> (le u4 u2) = true -> (le 0 u4) = true -> 0 = u3, (Term id_progAt ((Term id_Nil nil):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_0 nil):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_0 nil)::(model_nat u3)::nil)).
Definition F_233 : type_LF_195:= (fun    _ u2 u3 u4 _ _ => (0 = u3 -> (le u4 u2) = true -> (le 0 u4) = true -> 0 = u3, (Term id_0 nil)::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_0 nil):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_0 nil)::(model_nat u3)::nil)).
Definition F_227 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le (time (C u8 u9)) u4) = true -> (le u8 u2) = true -> (progAt (Cons (C u8 u9) u7) u4) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_230 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le (timeAt u7 u2) u4) = true -> (le u8 u2) = false -> (progAt (Cons (C u8 u9) u7) u4) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_250 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le (timeAt u7 u2) u4) = true -> (le u8 u2) = false -> (le (time (C u8 u9)) u4) = true -> (er (C u8 u9)) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::(model_nat u3)::nil)).
Definition F_254 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le (timeAt u7 u2) u4) = true -> (le u8 u2) = false -> (le (time (C u8 u9)) u4) = false -> (progAt u7 u4) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_progAt ((model_PLAN u7):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_257 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le (timeAt u7 u2) u4) = true -> (le u8 u2) = false -> (le u8 u4) = true -> (er (C u8 u9)) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::(model_nat u3)::nil)).
Definition F_263 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le (timeAt u7 u2) u4) = true -> (le u8 u2) = false -> (le u8 u4) = true -> u9 = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(model_nat u9)::(model_nat u3)::nil)).
Definition F_260 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le (timeAt u7 u2) u4) = true -> (le u8 u2) = false -> (le u8 u4) = false -> (progAt u7 u4) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_progAt ((model_PLAN u7):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_277 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((er (C u8 u9)) = u3 -> (le u4 u2) = true -> (le (timeAt u7 u2) u4) = true -> (le u8 u2) = false -> (le u8 u4) = false -> (le (time (C u8 u9)) u2) = true -> (progAt u7 u4) = u3, (Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((model_PLAN u7):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_281 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt u7 u2) = u3 -> (le u4 u2) = true -> (le (timeAt u7 u2) u4) = true -> (le u8 u2) = false -> (le u8 u4) = false -> (le (time (C u8 u9)) u2) = false -> (progAt u7 u4) = u3, (Term id_progAt ((model_PLAN u7):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_progAt ((model_PLAN u7):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_284 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => (u9 = u3 -> (le u4 u2) = true -> (le (timeAt u7 u2) u4) = true -> (le u8 u2) = false -> (le u8 u4) = false -> (le (time (C u8 u9)) u2) = true -> (progAt u7 u4) = u3, (model_nat u9)::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((model_PLAN u7):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_290 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => (u9 = u3 -> (le u4 u2) = true -> (le (timeAt u7 u2) u4) = true -> (le u8 u2) = false -> (le u8 u4) = false -> (le u8 u2) = true -> (progAt u7 u4) = u3, (model_nat u9)::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_timeAt ((model_PLAN u7):: (model_nat u2)::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((model_PLAN u7):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_236 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le u8 u4) = true -> (le u8 u2) = true -> (progAt (Cons (C u8 u9) u7) u4) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_303 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le u8 u4) = true -> (le u8 u2) = true -> (le (time (C u8 u9)) u4) = true -> (er (C u8 u9)) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::(model_nat u3)::nil)).
Definition F_307 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le u8 u4) = true -> (le u8 u2) = true -> (le (time (C u8 u9)) u4) = false -> (progAt u7 u4) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_progAt ((model_PLAN u7):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_310 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le u8 u4) = true -> (le u8 u2) = true -> (le u8 u4) = true -> (er (C u8 u9)) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::(model_nat u3)::nil)).
Definition F_313 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le u8 u4) = true -> (le u8 u2) = true -> (le u8 u4) = false -> (progAt u7 u4) = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_false nil)::(Term id_progAt ((model_PLAN u7):: (model_nat u4)::nil))::(model_nat u3)::nil)).
Definition F_316 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt (Cons (C u8 u9) u7) u2) = u3 -> (le u4 u2) = true -> (le u8 u4) = true -> (le u8 u2) = true -> (le u8 u4) = true -> u9 = u3, (Term id_progAt ((Term id_Cons ((Term id_C ((model_nat u8):: (model_nat u9)::nil)):: (model_PLAN u7)::nil)):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(model_nat u9)::(model_nat u3)::nil)).
Definition F_328 : type_LF_195:= (fun    _ u2 u3 u4 u8 u9 => ((er (C u8 u9)) = u3 -> (le u4 u2) = true -> (le u8 u4) = true -> (le u8 u2) = true -> (le u8 u4) = true -> (le (time (C u8 u9)) u2) = true -> u9 = u3, (Term id_er ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(model_nat u9)::(model_nat u3)::nil)).
Definition F_335 : type_LF_195:= (fun    _ u2 u3 u4 u8 u9 => (u9 = u3 -> (le u4 u2) = true -> (le u8 u4) = true -> (le u8 u2) = true -> (le u8 u4) = true -> (le (time (C u8 u9)) u2) = true -> u9 = u3, (model_nat u9)::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_true nil)::(model_nat u9)::(model_nat u3)::nil)).
Definition F_332 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt u7 u2) = u3 -> (le u4 u2) = true -> (le u8 u4) = true -> (le u8 u2) = true -> (le u8 u4) = true -> (le (time (C u8 u9)) u2) = false -> u9 = u3, (Term id_progAt ((model_PLAN u7):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((Term id_time ((Term id_C ((model_nat u8):: (model_nat u9)::nil))::nil)):: (model_nat u2)::nil))::(Term id_false nil)::(model_nat u9)::(model_nat u3)::nil)).
Definition F_338 : type_LF_195:= (fun   u7 u2 u3 u4 u8 u9 => ((progAt u7 u2) = u3 -> (le u4 u2) = true -> (le u8 u4) = true -> (le u8 u2) = true -> (le u8 u4) = true -> (le u8 u2) = false -> u9 = u3, (Term id_progAt ((model_PLAN u7):: (model_nat u2)::nil))::(model_nat u3)::(Term id_le ((model_nat u4):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u4)::nil))::(Term id_true nil)::(Term id_le ((model_nat u8):: (model_nat u2)::nil))::(Term id_false nil)::(model_nat u9)::(model_nat u3)::nil)).

Definition LF_195 := [F_195, F_209, F_215, F_221, F_224, F_233, F_227, F_230, F_250, F_254, F_257, F_263, F_260, F_277, F_281, F_284, F_290, F_236, F_303, F_307, F_310, F_313, F_316, F_328, F_335, F_332, F_338].


Function f_195 (u1: PLAN) (u2: nat) {struct u1} : nat :=
 match u1, u2 with
| Nil, _ => 0
| (Cons (C u8 u9) u7), _ => 0
end.


Hypothesis true_155: forall u1 u2 u3, (le u1 u2) = true -> (le u3 u1) = true -> (le u3 u2) = false -> False.

Lemma main_195 : forall F, In F LF_195 -> forall u1, forall u2, forall u3, forall u4, forall u5, forall u6, (forall F', In F' LF_195 -> forall e1, forall e2, forall e3, forall e4, forall e5, forall e6, less (snd (F' e1 e2 e3 e4 e5 e6)) (snd (F u1 u2 u3 u4 u5 u6)) -> fst (F' e1 e2 e3 e4 e5 e6)) -> fst (F u1 u2 u3 u4 u5 u6).
Proof.
intros F HF u1 u2 u3 u4 u5 u6; case_In HF; intro Hind.

	(* GENERATE on [ 195 ] *)

rename u1 into _u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u1 into u1. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 

revert Hind.

pattern u1, u2, (f_195 u1 u2). apply f_195_ind.

(* case [ 209 ] *)

intros _u1 _u2.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
assert (Hind := HFabs0 F_209). clear HFabs0.
assert (HFabs0 : fst (F_209 Nil _u2 u3 u4 0 0)).
apply Hind. trivial_in 1. unfold snd. unfold F_209. unfold F_195. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_195. unfold F_209.
auto.



intros _u1 _u2. intro u8. intro u9. intro u7.  intro eq_1. intro. intro Heq2. rewrite <- Heq2.  intro HFabs0.
case_eq (le (time (C u8 u9)) _u2); [intro H | intro H].

(* case [ 215 ] *)

assert (Hind := HFabs0 F_215). clear HFabs0.
assert (HFabs0 : fst (F_215 u7 _u2 u3 u4 u8 u9)).
apply Hind. trivial_in 2. unfold snd. unfold F_215. unfold F_195. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_195. unfold F_215. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.


(* case [ 221 ] *)

assert (Hind := HFabs0 F_221). clear HFabs0.
assert (HFabs0 : fst (F_221 u7 _u2 u3 u4 u8 u9)).
apply Hind. trivial_in 3. unfold snd. unfold F_221. unfold F_195. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_195. unfold F_221. simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). 
auto.





	(* REWRITING on [ 209 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_224). clear Hind.
assert (HFabs1 : fst (F_224 Nil u2 u3 u4 0 0)).
apply Res. trivial_in 4. unfold snd. unfold F_224. unfold F_209. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_209. unfold fst in HFabs1. unfold F_224 in HFabs1.   
pattern u4. simpl (progAt _ _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 215 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_227). clear Hind.
assert (HFabs1 : fst (F_227 u7 u2 u3 u4 u8 u9)).
apply Res. trivial_in 6. unfold snd. unfold F_227. unfold F_215. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_215. unfold fst in HFabs1. unfold F_227 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 221 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_230). clear Hind.
assert (HFabs1 : fst (F_230 u7 u2 u3 u4 u8 u9)).
apply Res. trivial_in 7. unfold snd. unfold F_230. unfold F_221. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_221. unfold fst in HFabs1. unfold F_230 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 224 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into d_u5. rename u6 into d_u6. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. 
assert (Res := Hind F_233). clear Hind.
assert (HFabs1 : fst (F_233 Nil u2 u3 u4 0 0)).
apply Res. trivial_in 5. unfold snd. unfold F_233. unfold F_224. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_224. unfold fst in HFabs1. unfold F_233 in HFabs1.   
pattern u2. simpl (progAt _ _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 233 ] *)

unfold fst. unfold F_233.
auto.



	(* REWRITING on [ 227 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_236). clear Hind.
assert (HFabs1 : fst (F_236 u7 u2 u3 u4 u8 u9)).
apply Res. trivial_in 17. unfold snd. unfold F_236. unfold F_227. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_227. unfold fst in HFabs1. unfold F_236 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* TOTAL CASE REWRITING on [ 230 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (H: ((le (time (C u8 u9)) u4) = true) \/ ((le (time (C u8 u9)) u4) = false)). 

destruct ((le (time (C u8 u9)) u4)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_250). clear Hind.
assert (HFabs0 : fst (F_250 u7 u2 u3 u4 u8 u9)).
apply H1. trivial_in 8. unfold snd. unfold F_250. unfold F_230. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_230. unfold F_250. unfold fst in HFabs0. unfold F_250 in HFabs0. simpl in HFabs0. 
pattern (C u8 u9).
pattern u4.
pattern u7.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_254). clear Hind.
assert (HFabs0 : fst (F_254 u7 u2 u3 u4 u8 u9)).
apply H1. trivial_in 9. unfold snd. unfold F_254. unfold F_230. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_230. unfold F_254. unfold fst in HFabs0. unfold F_254 in HFabs0. simpl in HFabs0. 
pattern (C u8 u9).
pattern u4.
pattern u7.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 250 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_257). clear Hind.
assert (HFabs1 : fst (F_257 u7 u2 u3 u4 u8 u9)).
apply Res. trivial_in 10. unfold snd. unfold F_257. unfold F_250. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_250. unfold fst in HFabs1. unfold F_257 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 254 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_260). clear Hind.
assert (HFabs1 : fst (F_260 u7 u2 u3 u4 u8 u9)).
apply Res. trivial_in 12. unfold snd. unfold F_260. unfold F_254. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_254. unfold fst in HFabs1. unfold F_260 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 257 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_263). clear Hind.
assert (HFabs1 : fst (F_263 u7 u2 u3 u4 u8 u9)).
apply Res. trivial_in 11. unfold snd. unfold F_263. unfold F_257. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_257. unfold fst in HFabs1. unfold F_263 in HFabs1.   
pattern u8, u9. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 263 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
unfold fst. unfold F_263. specialize true_155 with (u1 := u4) (u2 := u2) (u3 := u8). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 260 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (H: ((le (time (C u8 u9)) u2) = true) \/ ((le (time (C u8 u9)) u2) = false)). 

destruct ((le (time (C u8 u9)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_277). clear Hind.
assert (HFabs0 : fst (F_277 u7 u2 u3 u4 u8 u9)).
apply H1. trivial_in 13. unfold snd. unfold F_277. unfold F_260. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_260. unfold F_277. unfold fst in HFabs0. unfold F_277 in HFabs0. simpl in HFabs0. 
pattern (C u8 u9).
pattern u2.
pattern u7.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_281). clear Hind.
assert (HFabs0 : fst (F_281 u7 u2 u3 u4 u8 u9)).
apply H1. trivial_in 14. unfold snd. unfold F_281. unfold F_260. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_260. unfold F_281. unfold fst in HFabs0. unfold F_281 in HFabs0. simpl in HFabs0. 
pattern (C u8 u9).
pattern u2.
pattern u7.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 277 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_284). clear Hind.
assert (HFabs1 : fst (F_284 u7 u2 u3 u4 u8 u9)).
apply Res. trivial_in 15. unfold snd. unfold F_284. unfold F_277. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_277. unfold fst in HFabs1. unfold F_284 in HFabs1.   
pattern u8, u9. simpl (er _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 281 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_195). clear Hind.
assert (HFabs1 : fst (F_195 u7 u2 u3 u4 0 0)).
apply Res. trivial_in 0. unfold snd. unfold F_195. unfold F_281. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_281. unfold fst in HFabs1. unfold F_195 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 284 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_290). clear Hind.
assert (HFabs1 : fst (F_290 u7 u2 u3 u4 u8 u9)).
apply Res. trivial_in 16. unfold snd. unfold F_290. unfold F_284. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_284. unfold fst in HFabs1. unfold F_290 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 290 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
unfold fst. unfold F_290. specialize true_157 with (u1 := u8) (u2 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 236 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (H: ((le (time (C u8 u9)) u4) = true) \/ ((le (time (C u8 u9)) u4) = false)). 

destruct ((le (time (C u8 u9)) u4)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_303). clear Hind.
assert (HFabs0 : fst (F_303 u7 u2 u3 u4 u8 u9)).
apply H1. trivial_in 18. unfold snd. unfold F_303. unfold F_236. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_236. unfold F_303. unfold fst in HFabs0. unfold F_303 in HFabs0. simpl in HFabs0. 
pattern (C u8 u9).
pattern u4.
pattern u7.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_307). clear Hind.
assert (HFabs0 : fst (F_307 u7 u2 u3 u4 u8 u9)).
apply H1. trivial_in 19. unfold snd. unfold F_307. unfold F_236. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_236. unfold F_307. unfold fst in HFabs0. unfold F_307 in HFabs0. simpl in HFabs0. 
pattern (C u8 u9).
pattern u4.
pattern u7.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 303 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_310). clear Hind.
assert (HFabs1 : fst (F_310 u7 u2 u3 u4 u8 u9)).
apply Res. trivial_in 20. unfold snd. unfold F_310. unfold F_303. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_303. unfold fst in HFabs1. unfold F_310 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 307 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_313). clear Hind.
assert (HFabs1 : fst (F_313 u7 u2 u3 u4 u8 u9)).
apply Res. trivial_in 21. unfold snd. unfold F_313. unfold F_307. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_307. unfold fst in HFabs1. unfold F_313 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* REWRITING on [ 310 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_316). clear Hind.
assert (HFabs1 : fst (F_316 u7 u2 u3 u4 u8 u9)).
apply Res. trivial_in 22. unfold snd. unfold F_316. unfold F_310. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_310. unfold fst in HFabs1. unfold F_316 in HFabs1.   
pattern u8, u9. simpl (er _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 313 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
unfold fst. unfold F_313. specialize true_157 with (u1 := u8) (u2 := u4). intro L. intros. contradict L. (auto || symmetry; auto).



	(* TOTAL CASE REWRITING on [ 316 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (H: ((le (time (C u8 u9)) u2) = true) \/ ((le (time (C u8 u9)) u2) = false)). 

destruct ((le (time (C u8 u9)) u2)); auto.

destruct H as [H|H].

(* rewriting with the axiom [ 137 ] *)

assert (H1 := Hind F_328). clear Hind.
assert (HFabs0 : fst (F_328 Nil u2 u3 u4 u8 u9)).
apply H1. trivial_in 23. unfold snd. unfold F_328. unfold F_316. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_316. unfold F_328. unfold fst in HFabs0. unfold F_328 in HFabs0. simpl in HFabs0. 
pattern (C u8 u9).
pattern u2.
pattern u7.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.


(* rewriting with the axiom [ 138 ] *)

assert (H1 := Hind F_332). clear Hind.
assert (HFabs0 : fst (F_332 u7 u2 u3 u4 u8 u9)).
apply H1. trivial_in 25. unfold snd. unfold F_332. unfold F_316. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_316. unfold F_332. unfold fst in HFabs0. unfold F_332 in HFabs0. simpl in HFabs0. 
pattern (C u8 u9).
pattern u2.
pattern u7.
simpl (progAt _ _). cbv beta. try unfold progAt. try rewrite H. try rewrite H0. try unfold progAt in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.



	(* REWRITING on [ 328 ] *)

rename u1 into d_u1. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_335). clear Hind.
assert (HFabs1 : fst (F_335 Nil u2 u3 u4 u8 u9)).
apply Res. trivial_in 24. unfold snd. unfold F_335. unfold F_328. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_328. unfold fst in HFabs1. unfold F_335 in HFabs1.   
pattern u8, u9. simpl (er _). cbv beta.
 simpl. auto.



	(* TAUTOLOGY on [ 335 ] *)

unfold fst. unfold F_335.
auto.



	(* REWRITING on [ 332 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
assert (Res := Hind F_338). clear Hind.
assert (HFabs1 : fst (F_338 u7 u2 u3 u4 u8 u9)).
apply Res. trivial_in 26. unfold snd. unfold F_338. unfold F_332. rewrite_model. abstract solve_rpo_mul.
unfold fst. unfold F_332. unfold fst in HFabs1. unfold F_338 in HFabs1.   
pattern u8, u9. simpl (time _). cbv beta.
 simpl. auto.



	(* SUBSUMPTION on [ 338 ] *)

rename u1 into _u7. rename u2 into _u2. rename u3 into _u3. rename u4 into _u4. rename u5 into _u8. rename u6 into _u9. 
rename _u7 into u7. rename _u2 into u2. rename _u3 into u3. rename _u4 into u4. rename _u8 into u8. rename _u9 into u9. 
unfold fst. unfold F_338. specialize true_157 with (u1 := u8) (u2 := u2). intro L. intros. contradict L. (auto || symmetry; auto).



Qed.



(* the set of all formula instances from the proof *)
Definition S_195 := fun f => exists F, In F LF_195 /\ exists e1, exists e2, exists e3, exists e4, exists e5, exists e6, f = F e1 e2 e3 e4 e5 e6.

Theorem all_true_195: forall F, In F LF_195 -> forall u1: PLAN, forall u2: nat, forall u3: nat, forall u4: nat, forall u5: nat, forall u6: nat, fst (F u1 u2  u3  u4  u5  u6).
Proof.
let n := constr:(6) in
let p := constr:(S(S(n))) in
intros;
let G := fresh "G" in
let x := fresh "x" in
apply wf_subset with (R:=@snd_rpo_mul P Prop max_size) (S:=S_195);
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_195;
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.


Theorem true_195: forall (u1: PLAN) (u2: nat) (u3: nat) (u4: nat), (progAt u1 u2) = u3 -> (le u4 u2) = true -> (le (timeAt u1 u2) u4) = true -> (progAt u1 u4) = u3.
Proof.
do 4 intro.
apply (all_true_195 F_195);
 (trivial_in 0) ||
 (repeat constructor).
Qed.
