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
Require Import core.Certification.
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import transformations.Moore2Mealy.Moore.
Require Import transformations.Moore2Mealy.Moore2Mealy.


(*************************************************************)
(** * Surjectivity of CoqTL                                  *)
(*************************************************************)

(** Surjectivity on model elements                           *)

Theorem Surjectivity_elem :
forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
      In te (allModelElements (execute tr sm)) ->
      (exists (sp : list SourceModelElement),
          In sp (allTuples tr sm) /\
          In te (instantiatePattern tr sm sp)).
Proof.
    apply tr_execute_in_elements.
Qed.


(** Surjectivity on model links                              *)

Theorem Surjectivity_links :
forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
      In tl (allModelLinks (execute tr sm)) ->
      (exists (sp : list SourceModelElement),
          In sp (allTuples tr sm) /\
          In tl (applyPattern tr sm sp)).
Proof.
    apply tr_execute_in_links.
Qed.