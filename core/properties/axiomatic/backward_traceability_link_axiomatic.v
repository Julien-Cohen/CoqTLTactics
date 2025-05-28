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
(** * Backward_Traceability of Stdlib.L (Link)                  *)
(** * Using axiomatic semantics                              *)
(*************************************************************)

Require Import AxiomaticSemantics.

Section Backward_Traceability_Link.

Context {tc: TransformationConfiguration}.

(** 
 * FIXME I think Semantics.compute_trace could be replaced with axiomatic version.
 *)
Inductive is_tr_produced_link (tr: Transformation) (sm : SourceModel) (lk: TargetLinkType): Prop :=
| is_tr_produced_link_def : 
 AxiomaticSemantics.is_produced_link (Semantics.compute_trace tr sm) sm lk ->
    is_tr_produced_link tr sm lk.

(** 
 * FIXME Same question as in TranOnPiece_rel.
 *)
Inductive TranLkOnModel_rel (tr: Transformation) (sm : SourceModel) (sp: InputPiece) (lk: TargetLinkType): Prop :=
| TranLkOnModel_rel_def : 
    forall tra tlk, 
    apply_link_pattern_rel tra sm tlk lk ->
    (TraceLink.getSourcePiece tlk) = sp ->
            TranLkOnModel_rel tr sm sp lk.

Definition Backward_Traceability_link_axiomatic (tr: Transformation) :=
  forall (sm : SourceModel) (lk : TargetLinkType),
  is_tr_produced_link tr sm lk ->
      (exists (sp : InputPiece), 
          isTuple sm sp /\ TranLkOnModel_rel tr sm sp lk).

Theorem forall_Backward_Traceability_link_axiomatic :
  forall (tr: Transformation), Backward_Traceability_link_axiomatic tr.
Proof.
unfold Backward_Traceability_link_axiomatic.
intros.
destruct H.
destruct H.
destruct H.
remember H0 as ltr.
destruct H0.
eexists (TraceLink.getSourcePiece tlk).
split.
- apply prop7 in H.
  destruct H. destruct H. destruct H. destruct H4. destruct H5.
  unfold TraceLink.getSourcePiece. simpl. exact H0.
- assert (TraceLink.getSourcePiece tlk = TraceLink.getSourcePiece tlk). { reflexivity. }
  remember (TranLkOnModel_rel_def tr sm (TraceLink.getSourcePiece tlk) lk (Semantics.compute_trace tr sm) tlk ltr H0) as tranLkOnModel_rel_def.
  exact tranLkOnModel_rel_def.
Qed.

End Backward_Traceability_Link.