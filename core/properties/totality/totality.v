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
(** * Totality of CoqTL                                      *)
(*************************************************************)

(** Totality on model elements                               *)

Theorem Totality_elem :
forall (tr: Transformation) (sm : SourceModel) (te : TargetElementType),
      (exists (sp : list SourceElementType),
          In sp (allTuples tr sm) /\
          In te (instantiateTrOnPiece tr sm sp)) ->
          In te (execute tr sm).(modelElements).
Proof.
    apply tr_execute_in_elements.
Qed.

(*
Theorem Totality_elem:
forall (tr: Transformation) (sm : SourceModel) (sp : list SourceElementType) (te : TargetElementType),
In sp (allTuples tr sm) -> 
In te (instantiateOnPiece tr sm sp) ->
In te (allModelElements (execute tr sm)).
Proof.
    intros.
    apply tr_execute_in_elements.
    eexists sp. 
    auto.
Qed.

*)


(** Totality on model links                                  *)

Theorem Totality_links :
forall (tr: Transformation) (sm : SourceModel) (tl : TargetLinkType),
      (exists (sp : list SourceElementType),
          In sp (allTuples tr sm) /\
          In tl (applyTrOnPiece tr sm sp)) -> 
          In tl (execute tr sm).(modelLinks) .
Proof.
    apply tr_execute_in_links.
Qed.

(*
Theorem Totality_link:
forall (tr: Transformation) (sm : SourceModel) (sp : list SourceElementType) (tl : TargetLinkType),
In sp (allTuples tr sm) -> 
In tl (applyOnPiece tr sm sp) ->
In tl (allModelLinks (execute tr sm)).
Proof.
    intros.
    apply tr_execute_in_links.
    eexists sp. 
    auto.
Qed.

*)
