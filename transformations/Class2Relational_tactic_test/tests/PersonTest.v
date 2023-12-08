Require Import String.
Require Import List.

Require Import core.Model.
Require Import core.Semantics.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ConcreteSyntax.
Require Import core.utils.Utils.
Require Import transformations.Class2Relational_tactic_test.ClassMetamodel.
Require Import transformations.Class2Relational_tactic_test.RelationalMetamodel.
Require Import transformations.Class2Relational_tactic_test.Class2Relational_tactic_test.
Require Import transformations.Class2Relational_tactic_test.tests.PersonModel.

Compute (execute Class2Relational_tactic_test PersonModel).