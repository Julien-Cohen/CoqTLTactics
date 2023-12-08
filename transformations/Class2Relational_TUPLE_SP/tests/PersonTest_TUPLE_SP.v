Require Import String.
Require Import List.

Require Import core.Model.
Require Import core.Semantics.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ConcreteSyntax.
Require Import core.utils.Utils.

Require Import transformations.Class2Relational_TUPLE_SP.ClassMetamodel.
Require Import transformations.Class2Relational_TUPLE_SP.RelationalMetamodel.
Require Import transformations.Class2Relational_TUPLE_SP.tests.PersonModel.
Require Import transformations.Class2Relational_TUPLE_SP.Class2Relational_TUPLE_SP.

(* Expected output (short):
    Table id=0 name='Person'
      Column id=1 name='parent' reference='Person'
*)

Compute ((execute Class2Relational_TUPLE_SP PersonModel) ).
