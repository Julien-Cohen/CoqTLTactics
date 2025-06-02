From Stdlib 
  Require Import String EqNat List PeanoNat Lia FunctionalExtensionality.

From core 
  Require Import Semantics Syntax Model TransformationConfiguration Certification utils.Utils.

From core.modeling 
  Require Import ConcreteSyntax ModelingSemantics ModelingMetamodel ConcreteExpressions Parser.

Require Import transformations.Moore2Mealy.Moore2Mealy.

Require Import core.properties.distributivity.sampleMoore_distributivity.


(*************************************************************)
(** * Distributivity of CoqTL (Model)                        *)
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

