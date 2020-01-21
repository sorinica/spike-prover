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
  | id_Feuille
  | id_Noeud
  | id_false
  | id_true
  | id_Nil
  | id_Cons
  | id_app
  | id_flat
  | id_ins
  .

  Definition arity (f:symb) := 
    match f with
    | id_0 => term_spec.Free 0
    | id_S => term_spec.Free 1
    | id_Feuille => term_spec.Free 1
    | id_Noeud => term_spec.Free 2
    | id_false => term_spec.Free 0
    | id_true => term_spec.Free 0
    | id_Nil => term_spec.Free 0
    | id_Cons => term_spec.Free 2
    | id_app => term_spec.Free 2
    | id_flat => term_spec.Free 1
    | id_ins => term_spec.Free 2
    end. 
  
Definition status (f:symb) := 
     match f with
    | id_0 => rpo.Mul
    | id_S => rpo.Mul
    | id_Feuille => rpo.Mul
    | id_Noeud => rpo.Mul
    | id_false => rpo.Mul
    | id_true => rpo.Mul
    | id_Nil => rpo.Mul
    | id_Cons => rpo.Mul
    | id_app => rpo.Mul
    | id_flat => rpo.Mul
    | id_ins => rpo.Mul

    end.
  Definition index (f:symb) := 
     match f with
    | id_0 => 2
    | id_S => 3
    | id_Feuille => 4
    | id_Noeud => 5
    | id_false => 6
    | id_true => 7
    | id_Nil => 8
    | id_Cons => 9
    | id_app => 11
    | id_flat => 13
    | id_ins => 12
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

Inductive tree : Set :=
| Feuille : nat -> tree
| Noeud : tree -> tree -> tree.

Fixpoint model_tree (v: tree): term :=
match v with
| (Noeud t1 t2) => let t1' := model_tree t1 in let t2' := model_tree t2
in (Term id_Noeud (t1' :: t2' :: nil))
| (Feuille x) => let x' := model_nat x in (Term id_Feuille (x' :: nil))
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

Fixpoint app (l1 l2: list) : list := 
match l1 with
|Nil => l2
|(Cons x l) => (Cons x (app l l2))
end.

Fixpoint flat (t: tree) : list :=
match t with
|(Feuille x) => (Cons x Nil)
|(Noeud t1 t2) => (app (flat t1) (flat t2))
end.

Fixpoint ins (x:nat) (t:tree) : tree :=
match t with
|(Feuille y) => (Noeud (Feuille x) (Feuille y))
|(Noeud t1 t2) => (Noeud (ins x t1) t2)
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

Lemma model_tree_Feuille: forall (u1: nat), model_tree (Feuille u1) = (Term id_Feuille ((model_nat u1)::nil)).
Proof.
auto.
Qed.

Lemma model_tree_Noeud: forall (u1: tree), forall (u2: tree), model_tree (Noeud u1 u2) = (Term id_Noeud ((model_tree u1):: (model_tree u2)::nil)).
Proof.
auto.
Qed.

Lemma model_bool_false: model_bool false = (Term id_false nil).
Proof.
auto.
Qed.

Lemma model_bool_true: model_bool true = (Term id_true nil).
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



Hint Rewrite model_list_Nil model_list_Cons : model_list.
Hint Rewrite model_bool_false model_bool_true : model_bool.
Hint Rewrite model_nat_0 model_nat_S : model_nat.
Hint Rewrite model_tree_Feuille model_tree_Noeud : model_tree.


Ltac rewrite_model := autorewrite with model_list model_bool model_nat model_tree.