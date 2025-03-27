
Require Import String.
Require Import EqNat.
Require Import List.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.

Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.utils.Utils.
Require Import core.Metamodel.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import transformations.Moore2Mealy.Moore2Mealy.

(*************************************************************)
(** * Distributivity of CoqTL (Elem)                         *)
(** * Using axiomatic semantics                              *)
(*************************************************************)


(*************************************************************)
(** * This file is presented as proof of concept to          *)
(** * demonstrate how to define Distributivity axiomatically *)
(** * and how to use it to prove Monotonicity(ifDistrThenMon)*)
(*************************************************************)

Definition Model_elem_incl {MM : Metamodel} (m1 m2: Model MM) : Prop := 
  incl m1.(modelElements) m2.(modelElements). 

Inductive isUnionElems {MM : Metamodel} (m1 m2: Model MM) (union: Model MM): Prop :=
| Union_elem_intro : 
  (forall e, (List.In e m1.(modelElements) \/ List.In e m2.(modelElements)) <-> List.In e union.(modelElements))
      -> (isUnionElems m1 m2 union).

Lemma Union_exists_sub_model_elems :
  forall sm1 su,
    Model_elem_incl sm1 su ->
      exists sm2:SourceModel,
        isUnionElems sm1 sm2 su.
Proof.
  intros.
  exists su.
  apply Union_elem_intro.
  intros; crush.
Qed.

Definition Monotonicity' {tc: TransformationConfiguration} 
   (tr: Transformation) :=
forall sm1 sm2,
    Model_elem_incl sm1 sm2 ->
    Model_elem_incl (execute tr sm1) (execute tr sm2).  

Definition Distributivity' {tc:TransformationConfiguration} (tr: Transformation) :=
  forall (sm1 sm2 : SourceModel) (su: SourceModel),
    isUnionElems sm1 sm2 su ->
    isUnionElems (execute tr sm1) (execute tr sm2) (execute tr su).

Theorem ifDistrThenMon (tr: Transformation) :
  Distributivity' tr -> Monotonicity' tr.
Proof.
  intro.
  unfold Distributivity' in H.
  unfold Monotonicity' .
  intros.
  specialize (Union_exists_sub_model_elems) with sm1 sm2.
  intro.
  apply H1 in H0.
  destruct H0 as [sm3].
  specialize (H sm1 sm3 sm2).
  apply H in H0.
  clear H1 H.
  destruct H0.
  unfold Model_elem_incl.
  unfold incl.
  intros.
  apply H.
  left.
  exact H0.
Qed.




(* 

Definition Model_link_incl {MM : Metamodel} (m1 m2: Model MM) : Prop := 
  incl m1.(modelLinks) m2.(modelLinks). 
  
Inductive isUnionLinks {MM : Metamodel} (m1 m2: Model MM) (union: Model MM): Prop :=
| Union_link_intro : 
  (forall l, (List.In l m1.(modelLinks) \/ List.In l m2.(modelLinks) <-> List.In l union.(modelLinks)))
      -> (isUnionLinks m1 m2 union).

Lemma Union_get_sub_model_links :
  forall sm1 su,
    Model_link_incl sm1 su ->
      exists sm2:SourceModel,
        isUnionLinks sm1 sm2 su.
Proof.
  intros.
  exists su.
  apply Union_link_intro.
  intros; crush.
Qed.

Definition isUnion {MM : Metamodel} (m1 m2: Model MM) (union: Model MM) : Prop :=
  isUnionElems m1 m2 union /\ isUnionLinks m1 m2 union. 
  
*)