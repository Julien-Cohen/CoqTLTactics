From Stdlib 
  Require Import String EqNat List PeanoNat Lia FunctionalExtensionality.

From core 
  Require Import Semantics Syntax Model TransformationConfiguration utils.Utils.

From core 
  Require Certification.

From core.modeling
  Require Import ConcreteSyntax ModelingSemantics ModelingMetamodel ConcreteExpressions Parser.


(*************************************************************)
(** * Backward_Traceability of CoqTL (Link)                  *)
(** * Using operational semantics                            *)
(*************************************************************)

(** intuitively: I do not create from scratch target elements, a.k.a.
                 it does not exist a situation where a target element is not connected to any source pattern *)

Definition Backward_Traceability_link {tc: TransformationConfiguration}  (tr: Transformation) : Prop := 
    forall (sm : SourceModel) (tl : TargetLinkType),
    In tl (execute tr sm).(modelLinks) ->
    (exists (sp : InputPiece),
        In sp (allTuples tr sm) /\
        In tl (LegacySemantics.applyTrOnPiece tr sm sp)).


Theorem forall_Backward_Traceability_links {tc:TransformationConfiguration} :
    forall (tr: Transformation), Backward_Traceability_link tr.
Proof.
    unfold Backward_Traceability_link.
    apply Certification.tr_execute_in_links_legacy.
Qed.
