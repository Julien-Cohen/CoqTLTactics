Set Implicit Arguments.
From Stdlib Require Import List.

 Require Import ListUtils.

Require Import Metamodel.

(** * Model
  Each model is constructed by a list of {@code ElementType} and {@LinkType}. **)

Record Model (MM:Metamodel) :=
  {
    modelElements : list MM.(ElementType);
    modelLinks : list MM.(LinkType);
  }.

Definition Model_wellFormed {MM: Metamodel} (m: Model MM): Prop :=
  m.(modelElements) = nil -> m.(modelLinks) = nil.


Definition Model_incl {MM : Metamodel} (m1 m2: Model MM) : Prop :=
  (forall e,
    List.In e m1.(modelElements) ->  List.In e m2.(modelElements))
  /\
   (forall l,
       List.In l m1.(modelLinks) -> List.In l m2.(modelLinks) ).
   
Definition Model_equiv {MM : Metamodel} (m1 m2: Model MM) : Prop := 
  Model_incl m1 m2 /\ Model_incl m2 m1.

Definition Model_app {MM: Metamodel} (m1 m2: Model MM) := 
  {| 
    modelElements := app m1.(modelElements) m2.(modelElements) ;
    modelLinks := app m1.(modelLinks) m2.(modelLinks)
  |}.

Definition Model_concat {MM: Metamodel} (ms: list (Model MM)) := 
  {|
    modelElements := flat_map (@modelElements _) ms ;
    modelLinks := flat_map (@modelLinks _) ms
  |}.


(** Properties (equivalence relation) *)

Require Import Stdlib.Relations.Relation_Definitions.

Lemma Model_incl_refl : forall MM, reflexive (Model MM) Model_incl.
Proof. 
 unfold reflexive, Model_incl ; intros ; auto.
Qed.


Lemma Model_equiv_refl : forall MM, reflexive (Model MM) Model_equiv.
Proof.
 unfold reflexive, Model_equiv. intros. split ; apply Model_incl_refl.
Qed.

Lemma Model_equiv_symm : forall MM, symmetric (Model MM) Model_equiv.
Proof.
  unfold symmetric, Model_equiv; intros ; split ; destruct H; assumption. 
Qed.

Lemma Model_incl_trans : forall MM, transitive (Model MM) Model_incl.
Proof.
  unfold transitive, Model_incl ; intros.
  destruct H ; destruct H0 ; split ; intros ; eauto.
Qed.

Lemma Model_equiv_trans : forall MM, transitive (Model MM) Model_equiv.
Proof.
  unfold transitive, Model_equiv ; intros.
  destruct H ; destruct H0 ; split ; eapply Model_incl_trans ; eauto.
Qed.

Lemma Model_equiv_equiv : forall MM, equiv (Model MM) Model_equiv.
Proof.
    unfold equiv.
    intro ; split ; [ | split].
    apply Model_equiv_refl. 
    apply Model_equiv_trans.
    apply Model_equiv_symm.
Qed.
