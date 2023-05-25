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
  exists (t: Table_t),
    elements_proj (traceTrOnPiece Class2Relational cm [ClassElement c]) = [TableElement t].
Proof.
  eexists.
  reflexivity.
Qed.
