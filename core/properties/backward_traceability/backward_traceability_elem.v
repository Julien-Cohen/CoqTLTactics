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
(** * Backward_Traceability of CoqTL (Element)               *)
(** * Using operational semantics                            *)
(*************************************************************)

(** intuitively: I do not create from scratch target elements, a.k.a.
                 it does not exist a situation where a target element is not connected to any source pattern*)

Definition Backward_Traceability_elem {tc: TransformationConfiguration}  (tr: Transformation) : Prop := 
    forall (sm : SourceModel) (te : TargetElementType),
    In te (execute tr sm).(modelElements) ->
    (exists (sp : InputPiece),
        In sp (allTuples tr sm) /\
        In te (produced_elements (traceTrOnPiece tr sm sp))).

(* FIXME could consider to use prop in AxiomaticSemantics *)
Theorem forall_Backward_Traceability_elem {tc:TransformationConfiguration} :
forall (tr: Transformation), Backward_Traceability_elem tr.
Proof.
    unfold Backward_Traceability_elem.
    apply Certification.tr_execute_in_elements.
Qed.

    

