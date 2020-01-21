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
  | id_evenm
  | id_oddm
  | id_even
  | id_odd
  | id_evenr
  | id_oddc
  | id_plus
  .

  Definition arity (f:symb) := 
    match f with
    | id_0 => term_spec.Free 0
    | id_S => term_spec.Free 1
    | id_true => term_spec.Free 0
    | id_false => term_spec.Free 0
    | id_evenm => term_spec.Free 1
    | id_oddm => term_spec.Free 1
    | id_even => term_spec.Free 1
    | id_odd => term_spec.Free 1
    | id_evenr => term_spec.Free 1
    | id_oddc => term_spec.Free 1
    | id_plus => term_spec.Free 2
    end. 
  
Definition status (f:symb) := 
     match f with
    | id_0 => rpo.Mul
    | id_S => rpo.Mul
    | id_true => rpo.Mul
    | id_false => rpo.Mul
    | id_evenm => rpo.Mul
    | id_oddm => rpo.Mul
    | id_even => rpo.Mul
    | id_odd => rpo.Mul
    | id_evenr => rpo.Mul
    | id_oddc => rpo.Mul
    | id_plus => rpo.Mul

    end.
  Definition index (f:symb) := 
     match f with
    | id_0 => 2
    | id_S => 3
    | id_true => 4
    | id_false => 5
    | id_evenm => 10
    | id_oddm => 10
    | id_even => 11
    | id_odd => 11
    | id_evenr => 12
    | id_oddc => 13
    | id_plus => 7
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
| (S x) => let r := model_nat x in   (Term id_S (r::nil))
 end.

Fixpoint model_bool (v: bool): term :=
match v with
|true => (Term id_true nil)
|false => (Term id_false nil)
end.

Fixpoint plus (x y:nat): nat :=
match x with
| O => y
| (S x') => S (plus x' y)
end.

Fixpoint evenr (x: nat): bool :=
match x with
| 0 => true
| (S O) => false
| (S (S x')) => evenr x'
end.

Definition oddc (x: nat): bool :=
match evenr(x) with
| true => false
| false => true
end.

Fixpoint evenm (v:nat): bool:=
match v with
| O => true
| (S x) => oddm x
end
with
oddm (v:nat): bool :=
match v with
| O => false
| (S x) => evenm x
end.

Fixpoint even (v:nat): bool :=
match v with
  | 0 => true
  | S x => match odd x with
             | true => true
             | false => false
           end
end
with odd (v:nat): bool :=
match v with
  | 0 => false
  | S x => match even x with
             | true => true
             | false => false
           end
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



Hint Rewrite model_bool_true model_bool_false : model_bool.
Hint Rewrite model_nat_0 model_nat_S : model_nat.


Ltac rewrite_model := autorewrite with model_bool model_nat.