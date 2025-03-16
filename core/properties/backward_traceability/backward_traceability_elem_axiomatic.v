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
(** * Backward_Traceability of CoqTL (Elem)                  *)
(** * Using axiomatic semantics                              *)
(*************************************************************)

Require Import AxiomaticSemantics.

Section Backward_Traceability.

Context {tc: TransformationConfiguration}.


(** 
 * FIXME Since the axiomatic semantic is abstract,
         Should we establish relation between sp and te
         without exposing implementation detail of TraceLink?
         Concretely, my proposal is via TranOnPiece_rel below.
 *)
Inductive TranOnPiece_rel (tr: Transformation) (sm : SourceModel) (sp: InputPiece) (te: TargetElementType) : Prop :=
  | TranOnPiece_rel_def : forall tl, 
  traceTrOnPiece_rel tr sm sp tl ->
    tl.(TraceLink.produced) = te ->
        TranOnPiece_rel tr sm sp te.

Definition Backward_Traceability_elem_axiomatic (tr: Transformation) :=
  forall (sm : SourceModel) (te : TargetElementType),
  AxiomaticSemantics.is_produced_element tr sm te ->
      (exists (sp : InputPiece), 
          isTuple sm sp /\ TranOnPiece_rel tr sm sp te).

Theorem forall_Backward_Traceability_elem_axiomatic :
  forall (tr: Transformation), Backward_Traceability_elem_axiomatic tr.
Proof.
unfold Backward_Traceability_elem_axiomatic.
intros.
destruct H. destruct H.
eexists sp.
split.
- exact H0.
- remember ({| TraceLink.source := a; TraceLink.produced := b; TraceLink.linkPattern := c |}) as tl.
  assert (TraceLink.produced tl = b). { rewrite Heqtl. simpl. reflexivity. }
  remember (TranOnPiece_rel_def tr sm sp b tl H H2) as trOnPiece_rel_def.
  exact trOnPiece_rel_def.
Qed.

End Backward_Traceability.
