Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import Expressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.


Theorem Distributivity_instantiate:
forall (tc: TransformationConfiguration) (tr: Transformation) (sm: SourceModel) (l1 l2: list (list SourceModelElement)),
  (flat_map (instantiatePattern tr sm) (l1 ++ l2)) = 
    flat_map (instantiatePattern tr sm) l1 ++ flat_map (instantiatePattern tr sm) l2.
Proof.
 intros.
 apply flat_map_app.
Qed.

Theorem Distributivity_apply:
forall (tc: TransformationConfiguration) (tr: Transformation) (sm: SourceModel) (l1 l2: list (list SourceModelElement)),
  flat_map (applyPattern tr sm) (l1 ++ l2) = 
    flat_map (applyPattern tr sm) l1 ++ flat_map (applyPattern tr sm) l2.
Proof.
 intros.
 apply flat_map_app.
Qed.

