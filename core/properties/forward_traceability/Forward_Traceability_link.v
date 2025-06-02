From Stdlib 
  Require Import String EqNat List PeanoNat Lia FunctionalExtensionality.

From core 
  Require Import Semantics Syntax Model TransformationConfiguration utils.Utils.

From core 
  Require Certification.

From core.modeling
  Require Import ConcreteSyntax ModelingSemantics ModelingMetamodel ConcreteExpressions Parser.


(*************************************************************)
(** * Forward_Traceability of CoqTL (Link)                   *)
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
