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
(** * Surjectivity of CoqTL                                  *)
(*************************************************************)

(** Surjectivity on model elements                           *)

(* Theorem Surjectivity_elem {tc:TransformationConfiguration} :
forall (tr: Transformation) (sm : SourceModel) (te : TargetElementType),
      In te (execute tr sm).(modelElements) ->
      (exists (sp : InputPiece),
          In sp (allTuples tr sm) /\
          In te (produced_elements (traceTrOnPiece tr sm sp))).
Proof.
    apply Certification.tr_execute_in_elements.
Qed. *)

Require Import AxiomaticSemantics.

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

Theorem Surjectivity_elem {tc:TransformationConfiguration} :
forall (tr: Transformation) (sm : SourceModel) (te : TargetElementType),
    AxiomaticSemantics.is_produced_element tr sm te ->
        (exists (sp : InputPiece), 
            isTuple sm sp /\ TranOnPiece_rel tr sm sp te).
Proof.
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

(** Surjectivity on model links                              *)

(* Theorem Surjectivity_links {tc:TransformationConfiguration} :
forall (tr: Transformation) (sm : SourceModel) (tl : TargetLinkType),
      In tl (execute tr sm).(modelLinks) ->
      (exists (sp : InputPiece),
          In sp (allTuples tr sm) /\
          In tl (LegacySemantics.applyTrOnPiece tr sm sp)).
Proof.
    apply Certification.tr_execute_in_links_legacy.
Qed.  *)

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

Theorem Surjectivity_link {tc:TransformationConfiguration} :
forall (tr: Transformation) (sm : SourceModel) (lk : TargetLinkType),
    is_tr_produced_link tr sm lk ->
        (exists (sp : InputPiece), 
            isTuple sm sp /\ TranLkOnModel_rel tr sm sp lk).
Proof.
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
