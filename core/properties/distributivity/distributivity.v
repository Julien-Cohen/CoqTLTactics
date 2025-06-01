
From Stdlib Require Import String.
From Stdlib Require Import EqNat.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.

Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import transformations.Moore2Mealy.Moore2Mealy.
Require Import core.properties.monotonicity.Moore2Mealy_monotonicity_elem_witness.
Require Import core.properties.distributivity.sampleMoore_distributivity.


(*************************************************************)
(** * Distributivity of  CoqTL (Model)                        *)
(** * Using operational semantics                            *)
(*************************************************************)

Definition Distributivity {tc:TransformationConfiguration} (tr: Transformation) :=
forall (sm1 sm2 : SourceModel),
  execute tr (Model_app sm1 sm2) =
  Model_app (execute tr sm1) (execute tr sm2).

Lemma Moore2Mealy_non_distributive_contrapos:
  exists sm1 sm2 : SourceModel,
    ~ (execute Moore2Mealy (Model_app sm1 sm2) =
      Model_app (execute Moore2Mealy sm1) (execute Moore2Mealy sm2)).
Proof.
exists sampleMoore_distributivity.Moore_m1.
exists sampleMoore_distributivity.Moore_m2.
compute.
discriminate.
Qed.

Lemma Moore2Mealy_non_distributive : ~ (Distributivity Moore2Mealy).
Proof.
unfold Distributivity.
intro.
specialize Moore2Mealy_non_distributive_contrapos ; intro H2.
crush.
Qed.

Lemma exists_non_distributive  :
    exists tr, ~ (Distributivity tr).
Proof.
  exists Moore2Mealy.
  apply Moore2Mealy_non_distributive.
Qed.


Theorem Non_Distributivity:
  ~ (forall tr, (Distributivity tr)).
Proof.
  intro.
  specialize (exists_non_distributive).
  intro.
  destruct H0.
  specialize (H x).
  contradiction.
Qed.

