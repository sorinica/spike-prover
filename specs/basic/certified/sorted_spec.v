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
  | id_Nil
  | id_Cons
  | id_true
  | id_false
  | id_sorted
  | id_leq
  | id_length
  | id_insert
  | id_isort
  | id_eq_nat
  .

  Definition arity (f:symb) := 
    match f with
    | id_0 => term_spec.Free 0
    | id_S => term_spec.Free 1
    | id_Nil => term_spec.Free 0
    | id_Cons => term_spec.Free 2
    | id_true => term_spec.Free 0
    | id_false => term_spec.Free 0
    | id_sorted => term_spec.Free 1
    | id_leq => term_spec.Free 2
    | id_length => term_spec.Free 1
    | id_insert => term_spec.Free 2
    | id_isort => term_spec.Free 1
    | id_eq_nat => term_spec.Free 2
    end. 
  
Definition status (f:symb) := 
     match f with
    | id_0 => rpo.Mul
    | id_S => rpo.Mul
    | id_Nil => rpo.Mul
    | id_Cons => rpo.Mul
    | id_true => rpo.Mul
    | id_false => rpo.Mul
    | id_sorted => rpo.Mul
    | id_leq => rpo.Mul
    | id_length => rpo.Mul
    | id_insert => rpo.Mul
    | id_isort => rpo.Mul
    | id_eq_nat => rpo.Mul

    end.
  Definition index (f:symb) := 
     match f with
    | id_0 => 2
    | id_S => 3
    | id_Nil => 4
    | id_Cons => 5
    | id_true => 6
    | id_false => 7
    | id_sorted => 16
    | id_leq => 11
    | id_length => 12
    | id_insert => 17
    | id_isort => 18
    | id_eq_nat => 13
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
   
Fixpoint model_nat (v: nat): term :=
match v with
| O => (Term id_0 nil)
| (S x) => let x' := model_nat x in   (Term id_S (x'::nil))
 end.

Fixpoint model_bool (v: bool): term :=
match v with
|true => (Term id_true nil)
|false => (Term id_false nil)
end.

Inductive list : Set :=
|Nil : list
|Cons : nat -> list -> list.

Fixpoint model_list (v:list) : term :=
match v with
| Nil => (Term id_Nil nil)
| (Cons x l) => let x' := model_nat x in let l' := model_list l in
(Term id_Cons (x' :: l' :: nil))  
end.

Fixpoint eq_nat (n1:nat) (n2:nat): bool :=
match n1, n2 with
| O, O => true
| O, _ => false
| _, O => false
| (S x), (S y) => eq_nat x y
end.

Fixpoint leq (n1:nat) (n2: nat) : bool := 
match n1, n2 with
|O, _ => true
| _, 0 => false
| (S x), (S y) => leq x y
end.

Fixpoint length (l:list): nat :=
match l with
| Nil => O
| Cons _ y => S (length y)
end.

Fixpoint insert (x:nat) (l:list): list :=
match l with
|Nil => Cons x Nil
|Cons h tl => match leq x h with |true => Cons x l |false => Cons h (insert x tl) end
end.

Fixpoint isort (l:list): list:=
match l with
|Nil => Nil
|Cons h tl =>insert h (isort tl)
end.

Definition head_sorted (l : list) : bool := match l with
Cons a (Cons b _) => leq a b | _ => true end.

Fixpoint sorted (l : list) : bool := match l with
Cons a tl => if head_sorted (Cons a tl) then sorted tl else false | Nil => true end.




(** Initialisation of proof process *)
Lemma model_nat_0: model_nat 0 = (Term id_0 nil).
Proof.
auto.
Qed.

Lemma model_nat_S: forall (u1: nat), model_nat (S u1) = (Term id_S ((model_nat u1)::nil)).
Proof.
auto.
Qed.

Lemma model_list_Nil: model_list Nil = (Term id_Nil nil).
Proof.
auto.
Qed.

Lemma model_list_Cons: forall (u1: nat), forall (u2: list), model_list (Cons u1 u2) = (Term id_Cons ((model_nat u1):: (model_list u2)::nil)).
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



Hint Rewrite model_list_Nil model_list_Cons : model_list.
Hint Rewrite model_nat_0 model_nat_S : model_nat.
Hint Rewrite model_bool_true model_bool_false : model_bool.


Ltac rewrite_model := autorewrite with model_list model_nat model_bool.