From Stdlib Require Import String.
From Stdlib Require Import EqNat.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.

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
(** * Forward_Traceability of Stdlib.L (Link)                   *)
(** * Using operational semantics                            *)
(*************************************************************)

(** intuitively: I do not miss source elements, a.k.a. 
                 it does not exist a situation where a (transformed) source pattern is not connected to any target element*)

Definition Forward_Traceability_links {tc: TransformationConfiguration} (tr: Transformation) :=
forall (sm : SourceModel) (tl : TargetLinkType),
    (exists (sp : InputPiece),
        In sp (allTuples tr sm) /\
        In tl (LegacySemantics.applyTrOnPiece tr sm sp)) -> 
        In tl (execute tr sm).(modelLinks) .

Theorem forall_Forward_Traceability_links {tc:TransformationConfiguration} :
forall (tr: Transformation), Forward_Traceability_links tr.
Proof.
    unfold Forward_Traceability_links.
    apply Certification.tr_execute_in_links_legacy.
Qed.


















(*

(** FIXME M.T. different ways to write Forward_Traceability *)
(**            we want to choose the one that is duality of *)
(**            Backward_Traceability.  *)

Theorem Totality_link:
forall (tr: Transformation) (sm : SourceModel) (sp : InputPiece) (tl : TargetLinkType),
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
