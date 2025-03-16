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



(*************************************************************)
(** * Forward_Traceability of CoqTL (Elem)                   *)
(** * Using operational semantics                            *)
(*************************************************************)

(** intuitively: I do not miss source elements, a.k.a. 
                 it does not exist a situation where a (transformed) source pattern is not connected to any target element*)


Definition Forward_Traceability_elem {tc: TransformationConfiguration} (tr: Transformation) :=
    forall (sm : SourceModel) (te : TargetElementType),
    (exists (sp : InputPiece),
        In sp (allTuples tr sm) /\
        In te (produced_elements (traceTrOnPiece tr sm sp))) ->
        In te (execute tr sm).(modelElements).

Theorem forall_Forward_Traceability_elem {tc:TransformationConfiguration} :
    forall (tr: Transformation), Forward_Traceability_elem tr.
Proof.
    unfold Forward_Traceability_elem.
    apply Certification.tr_execute_in_elements.
Qed.


















(*

(** FIXME M.T. different ways to write Forward_Traceability *)
(**            we want to choose the one that is duality of *)
(**            Backward_Traceability.  *)
Theorem Forward_Traceability_elem' {tc:TransformationConfiguration} :
forall (tr: Transformation) (sm : SourceModel) (sp : InputPiece),
      In sp (allTuples tr sm) ->
      (forall (te : TargetElementType),
        In te (produced_elements (traceTrOnPiece tr sm sp)) -> 
        In te (execute tr sm).(modelElements)).
Proof.
    intros.
    apply Certification.tr_execute_in_elements.
    exists sp.
    split.
    auto.
    auto.
Qed.

Theorem Totality_elem:
forall (tr: Transformation) (sm : SourceModel) (sp : InputPiece) (te : TargetElementType),
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


