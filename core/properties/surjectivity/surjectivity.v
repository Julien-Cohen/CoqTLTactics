
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
Require        core.Certification.
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

(** FIXME counterexample: a transformation that produce no links, and we can't ask it to produce any link *)
Definition Surjectivity_fun {tc:TransformationConfiguration} :=
forall (tm: TargetModel) (tr:Transformation), exists (sm: SourceModel), (execute tr sm) = tm. 

Definition Surjectivity_fun_tr {tc:TransformationConfiguration} (tr:Transformation) :=
forall (tm: TargetModel), exists (sm: SourceModel), (execute tr sm) = tm.