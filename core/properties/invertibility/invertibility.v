
From Stdlib Require Import String EqNat List PeanoNat Lia FunctionalExtensionality.

Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require        core.Certification.
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.properties.surjectivity.Moore2Mealy_surjectivity_model_witness.
Require Import core.properties.surjectivity.sampleMealy_surjectivity_model.

(*************************************************************)
(** * Surjectivity of CoqTL (Model)                          *)
(** * Using operational semantics                            *)
(*************************************************************)

Definition Right_Invertibility {tc:TransformationConfiguration} (tr:Transformation) :=
    exists (tr_inv: Transformation (tc:= InverseTC tc)), forall (sm:SourceModel) (tm:TargetModel),
      (execute tr sm) = tm -> (execute tr_inv tm) = sm.

Definition Left_Invertibility {tc:TransformationConfiguration} (tr:Transformation) :=
    exists (tr_inv: Transformation (tc:= InverseTC tc)), forall (sm:SourceModel) (tm:TargetModel),
      (execute tr_inv tm) = sm -> (execute tr sm) = tm.


