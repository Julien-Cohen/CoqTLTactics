Require Import String.
Require Import List.

Require Import core.Model.
Require Import core.Semantics.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ConcreteSyntax.
Require Import core.utils.Utils.

Require Import transformations.Class2Relational_TUPLES.ClassMetamodel.
Require Import transformations.Class2Relational_TUPLES.RelationalMetamodel.
Require Import transformations.Class2Relational_TUPLES.tests.PersonModel.
Require Import transformations.Class2Relational_TUPLES.Class2Relational_TUPLES.

(* Expected output (short):
    Table id=0 name='Person'
      Column id=1 name='parent' reference='Person'
*)

Compute ((execute Class2Relational_TUPLES PersonModel) ).
