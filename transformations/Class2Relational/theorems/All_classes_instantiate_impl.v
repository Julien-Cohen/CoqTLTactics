Require Import String.

Require Import core.utils.Utils.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

Require Import core.utils.CpdtTactics.

Theorem All_classes_instantiate_impl:
  forall (cm : ClassModel) (c: Class_t),
  exists (t: Table),
    instantiatePattern Class2Relational cm [ClassMetamodel.lift_EKind Class_K c] = [RelationalMetamodel.toObject TableClass t].
Proof.
  eexists.
  reflexivity.
Qed.
