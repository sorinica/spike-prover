Require Export List.

Require Import term.
Require Import rpo.

Require Export utils.
Require Export coccinelle_utils.

(** Translation of the specification *)
Module Specif.
  
  Inductive symb : Set := 
  | id_0
  | id_S
  | id_true
  | id_false
  | id_C
  | id_Nil
  | id_Cons
  | id_PLAN_eq
  | id_OBJ_eq
  | id_nat_eq
  | id_plus
  | id_le
  | id_time
  | id_timel
  | id_er
  | id_erl
  | id_memberC
  | id_memberT
  | id_memberE
  | id_sortedT
  | id_sortedE
  | id_listUpTo
  | id_wind
  | id_maxEr
  | id_acr
  | id_insAt
  | id_insIn
  | id_progAt
  | id_timeAt
  | id_firstAt
  | id_listAt
  | id_prog
  | id_acr1
  .

  Definition arity (f:symb) := 
    match f with
    | id_0 => term_spec.Free 0
    | id_S => term_spec.Free 1
    | id_true => term_spec.Free 0
    | id_false => term_spec.Free 0
    | id_C => term_spec.Free 2
    | id_Nil => term_spec.Free 0
    | id_Cons => term_spec.Free 2
    | id_PLAN_eq => term_spec.Free 2
    | id_OBJ_eq => term_spec.Free 2
    | id_nat_eq => term_spec.Free 2
    | id_plus => term_spec.Free 2
    | id_le => term_spec.Free 2
    | id_time => term_spec.Free 1
    | id_timel => term_spec.Free 1
    | id_er => term_spec.Free 1
    | id_erl => term_spec.Free 1
    | id_memberC => term_spec.Free 2
    | id_memberT => term_spec.Free 2
    | id_memberE => term_spec.Free 2
    | id_sortedT => term_spec.Free 1
    | id_sortedE => term_spec.Free 1
    | id_listUpTo => term_spec.Free 2
    | id_wind => term_spec.Free 4
    | id_maxEr => term_spec.Free 1
    | id_acr => term_spec.Free 4
    | id_insAt => term_spec.Free 3
    | id_insIn => term_spec.Free 3
    | id_progAt => term_spec.Free 2
    | id_timeAt => term_spec.Free 2
    | id_firstAt => term_spec.Free 2
    | id_listAt => term_spec.Free 2
    | id_prog => term_spec.Free 3
    | id_acr1 => term_spec.Free 4
    end. 
  
Definition status (f:symb) := 
     match f with
    | id_0 => rpo.Mul
    | id_S => rpo.Mul
    | id_true => rpo.Mul
    | id_false => rpo.Mul
    | id_C => rpo.Mul
    | id_Nil => rpo.Mul
    | id_Cons => rpo.Mul
    | id_PLAN_eq => rpo.Mul
    | id_OBJ_eq => rpo.Mul
    | id_nat_eq => rpo.Mul
    | id_plus => rpo.Mul
    | id_le => rpo.Mul
    | id_time => rpo.Mul
    | id_timel => rpo.Mul
    | id_er => rpo.Mul
    | id_erl => rpo.Mul
    | id_memberC => rpo.Mul
    | id_memberT => rpo.Mul
    | id_memberE => rpo.Mul
    | id_sortedT => rpo.Mul
    | id_sortedE => rpo.Mul
    | id_listUpTo => rpo.Mul
    | id_wind => rpo.Mul
    | id_maxEr => rpo.Mul
    | id_acr => rpo.Mul
    | id_insAt => rpo.Mul
    | id_insIn => rpo.Mul
    | id_progAt => rpo.Mul
    | id_timeAt => rpo.Mul
    | id_firstAt => rpo.Mul
    | id_listAt => rpo.Mul
    | id_prog => rpo.Mul
    | id_acr1 => rpo.Mul

    end.
  Definition index (f:symb) := 
     match f with
    | id_0 => 2
    | id_S => 3
    | id_true => 4
    | id_false => 5
    | id_C => 6
    | id_Nil => 7
    | id_Cons => 10
    | id_PLAN_eq => 17
    | id_OBJ_eq => 14
    | id_nat_eq => 11
    | id_plus => 12
    | id_le => 18
    | id_time => 8
    | id_timel => 13
    | id_er => 9
    | id_erl => 22
    | id_memberC => 19
    | id_memberT => 15
    | id_memberE => 16
    | id_sortedT => 27
    | id_sortedE => 32
    | id_listUpTo => 25
    | id_wind => 28
    | id_maxEr => 20
    | id_acr => 35
    | id_insAt => 26
    | id_insIn => 29
    | id_progAt => 30
    | id_timeAt => 23
    | id_firstAt => 24
    | id_listAt => 31
    | id_prog => 36
    | id_acr1 => 39
    end. 

  Definition max_size := 100.

End Specif.


(* Nat and comparisons *)
Module Nat <: decidable_set.S.

  Definition A:=nat.
  Definition eq_bool := utils.beq_nat.
  Definition eq_bool_ok := utils.beq_nat_ok.

End Nat. (*: decidable_set.S*)


(** Initialisation of Coccinelle *)
Module Symbols <: term_spec.Signature.

  Module Symb <: decidable_set.S.

    Definition A:=Specif.symb.

    Theorem symb_eq_dec: forall x y:A, {x=y}+{x<>y}.
    Proof.
    decide equality.
    Defined.

    Definition eq_bool := utils.eq_bool A symb_eq_dec.
    Definition eq_bool_ok := utils.eq_bool_ok A symb_eq_dec.

  End Symb. (* Symb : decidable_set.S *)

  Definition arity := Specif.arity.

End Symbols. (* Symbols : term_spec.Signature *)

Module Terms <: term_spec.Term := term.Make' Symbols Nat.
Module Rpo := coccinelle_utils.Make Terms.

Export Specif.
Export Rpo.

Theorem prec_eq_status : forall f g, utils.prec_eq symb index f g -> status f = status g.
Proof.
intros f g; case f; case g; reflexivity.
Qed.

Definition P := rpo.Build_Precedence status
    (utils.prec_bool symb index) (utils.prec_bool_ok symb index)  (utils.prec_antisym symb index) (utils.prec_transitive symb index) (utils.prec_eq_bool symb index) (utils.prec_eq_transitive symb index) (utils.prec_eq_refl symb index) (utils.prec_eq_bool_ok symb index) (utils.prec_eq_prec1 symb index) (utils.prec_eq_prec2 symb index) (utils.prec_eq_sym symb index) (utils.prec_not_prec_eq symb index) (prec_eq_status).

Notation less := (rpo_mul P (bb (empty_rpo_infos P max_size))).


(* Coq version of the specification. *) (* TODO: should be in Spec module but model_* *)
  Inductive OBJ:Set := C: nat -> nat -> OBJ.
Inductive PLAN:Set := Nil | Cons: OBJ -> PLAN -> PLAN.

Fixpoint nat_eq (m n:nat) : bool :=
match m, n with
|0, 0 => true
|S_, 0 => false
|0, S_ => false
| S x, S y => nat_eq x y
end.

Definition OBJ_eq (m n: OBJ) : bool :=
match m, n with
| C t1 e1, C t2 e2 => andb (nat_eq t1 t2) (nat_eq e1 e2)
end.

Fixpoint PLAN_eq (m n: PLAN) : bool :=
match m, n with
| Nil, Nil => true
| Nil, Cons _ _ => false
| Cons _ _, Nil => false
| Cons o1 l1, Cons o2 l2 => 
 match OBJ_eq o1 o2 with
  | true => PLAN_eq l1 l2
  | false => false
 end
end.

Fixpoint le (m n:nat): bool :=
match m,n with
| 0,_ => true
| S_, 0 => false
| S x, S y => le x y
end.

Definition time (o:OBJ) : nat :=
match o with
| C t e => t
end.

Fixpoint memberC (o1:OBJ) (p1:PLAN): bool :=
match p1 with
|Nil => false
| Cons o2 p2 =>  
  match OBJ_eq o1 o2 with
  |true => true
  |false => memberC o1 p2
 end
end.

Fixpoint memberT (t1:nat) (p1:PLAN): bool :=
match p1 with
|Nil => false
| Cons (C t2 e) p2 =>  
  match nat_eq t1 t2 with
  |true => true
  |false => memberT t1 p2
 end
end.

Fixpoint memberE (e1:nat) (p1:PLAN): bool :=
match p1 with
|Nil => false
| Cons (C t e2) p2 =>  
  match nat_eq e1 e2 with
  |true => true
  |false => memberE e1 p2
 end
end.

Definition timel (o:PLAN): nat :=
match o with 
| Nil => 0
| Cons o p => time o
end.

Definition er (o:OBJ) : nat :=
match o with
| C t e => e
end.

Definition erl (p:PLAN) : nat :=
match p with
| Nil => 0
| Cons o p' => er o
end.

Fixpoint sortedT (p:PLAN) : bool :=
match p with
| Nil => true
| Cons (C t1 e1) p1 => 
  match p1 with
  | Nil => true
  | Cons (C t2 e2) p2 => 
     match le t2 t1 with
       | true => sortedT p1
       | false => false
     end
  end
end.

Fixpoint sortedE (p:PLAN) : bool :=
match p with
| Nil => true
| Cons (C t1 e1) p1 => 
  match p1 with
  | Nil => true
  | Cons (C t2 e2) p2 => 
     match le e2 e1 with
       | false => sortedE p1
       | true => false
     end
  end
end.

Fixpoint listUpTo (p:PLAN) (t:nat) : PLAN :=
match p with
|Nil =>  Nil
|Cons (C t1 e1) p1 => 
  match le t1 t with
   | true => Cons (C t1 e1) Nil
   | false => Cons (C t1 e1) (listUpTo p1 t)
 end
end.
 
Fixpoint wind (p':PLAN) (t t1 t2: nat) : PLAN :=
match p' with
|Nil => Nil
|Cons (C t' e') p => 
 match le (plus t' t2) t with
  | false => wind p t  t1 t2
  | true => 
    match le (plus t' t1) t with
       | true => Cons (C t' e') Nil
       | false => Cons (C t' e') (wind p t t1 t2)
   end
 end
end.


Fixpoint maxEr (p':PLAN) : nat :=
match p' with
|Nil => 0
|Cons (C t e) p => 
  match le (maxEr p) e with 
  | true => e
  | false => maxEr p
 end
end.

Definition acr (p: PLAN) (t t2 t3: nat) : nat := 
   match sortedT p with
    | true => (match le t2 t3 with 
                       |false =>maxEr (wind p t t2 t3)
                       |true =>  0
                     end)
    | false => 0
  end.

Fixpoint insAt (p:PLAN) (t e:nat) : PLAN :=
match p with
| Nil => Cons(C t e) Nil
| Cons o pg =>
  match le (time o) t with
  | true => Cons (C t e) (Cons o pg)
  | false => insAt pg t e
  end
end.

Fixpoint insIn  (p:PLAN) (t e:nat) : PLAN :=
match p with
| Nil => Cons(C t e) Nil
| Cons o pg =>
  match le (er o) e with
  | true => insIn pg (time o) e
  | false => Cons (C t e) (Cons o pg)
  end
end.

Hint Unfold er. 
Hint Unfold time.

Fixpoint progAt (p:PLAN) (t:nat) : nat :=
match p with
| Nil => 0
| Cons o pg =>
  match le (time o) t with
  | true => er o
  | false => progAt pg t
  end
end.

Fixpoint timeAt (p: PLAN) (t:nat) : nat :=
match p with
|Nil => 0
|Cons o pg => 
  match le (time o) t with
   | true => time o
   | false => timeAt pg t
  end
end.

Fixpoint firstAt (p:PLAN) (t:nat) : OBJ :=
match p with
| Nil => C 0 0
| Cons o pg => 
  match le (time o) t with
    | true => o
    | false => firstAt pg t
  end
end.
 
Fixpoint listAt (p: PLAN) (t: nat) : PLAN :=
match p with 
|Nil => Nil
|Cons o pg => 
  match le (time o) t with
    | true => Cons o pg
    | false => listAt pg t
  end
end.
 
Fixpoint prog (p:PLAN) (t2 t3:nat) : PLAN :=
match p with
| Nil => Nil
| Cons o p =>
  match le (progAt (prog p t2 t3) (plus (time o) t3)) (er o) with
  | true => insAt (prog p t2 t3) (plus (time o) t3) (er o) 
  | false => insIn (prog p t2 t3) (plus (time o) t2) (er o)
  end
end.

Fixpoint model_nat (n:nat) : term :=
match n with
| 0 => Term id_0 nil
| S n' => Term id_S ((model_nat n')::nil)
end.

Definition model_bool (b:bool) : term :=
match b with
| true => Term id_true nil
| false => Term id_false nil
end.

Definition model_OBJ (o:OBJ) : term :=
match o with
| C x y => Term id_C ((model_nat x)::(model_nat y)::nil)
end.

Fixpoint model_PLAN (p:PLAN) : term :=
match p with
| Nil => Term id_Nil nil
| Cons o p => Term id_Cons ((model_OBJ o)::(model_PLAN p)::nil)
end.

Definition acr1 (p: PLAN) (t t2 t3: nat) : nat := 
   match sortedT p with
    | true => (match le t2 t3 with 
                       |false => progAt (prog p t2 t3) t 
                       |true =>  0
                     end)
    | false => 0
  end.





(** Initialisation of proof process *)
Lemma model_nat_0: model_nat 0 = (Term id_0 nil).
Proof.
auto.
Qed.

Lemma model_nat_S: forall (u1: nat), model_nat (S u1) = (Term id_S ((model_nat u1)::nil)).
Proof.
auto.
Qed.

Lemma model_bool_true: model_bool true = (Term id_true nil).
Proof.
auto.
Qed.

Lemma model_bool_false: model_bool false = (Term id_false nil).
Proof.
auto.
Qed.

Lemma model_OBJ_C: forall (u1: nat), forall (u2: nat), model_OBJ (C u1 u2) = (Term id_C ((model_nat u1):: (model_nat u2)::nil)).
Proof.
auto.
Qed.

Lemma model_PLAN_Nil: model_PLAN Nil = (Term id_Nil nil).
Proof.
auto.
Qed.

Lemma model_PLAN_Cons: forall (u1: OBJ), forall (u2: PLAN), model_PLAN (Cons u1 u2) = (Term id_Cons ((model_OBJ u1):: (model_PLAN u2)::nil)).
Proof.
auto.
Qed.



Hint Rewrite model_PLAN_Nil model_PLAN_Cons : model_PLAN.
Hint Rewrite model_bool_true model_bool_false : model_bool.
Hint Rewrite model_nat_0 model_nat_S : model_nat.
Hint Rewrite model_OBJ_C : model_OBJ.


Ltac rewrite_model := autorewrite with model_PLAN model_bool model_nat model_OBJ.