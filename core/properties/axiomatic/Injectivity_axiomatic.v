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
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import AxiomaticSemantics.

(*************************************************************)
(** * Injectivity of CoqTL                                   *)
(*************************************************************)

(** FIXME refer to comment from surjectivity_axiomatic.v *)
Inductive TranOnPiece_rel {tc: TransformationConfiguration} (tr: Transformation) (sm : SourceModel) (sp: InputPiece) (te: TargetElementType) : Prop :=
  | TranOnPiece_rel_def : forall tl, 
  traceTrOnPiece_rel tr sm sp tl ->
    tl.(TraceLink.produced) = te ->
        TranOnPiece_rel tr sm sp te.


(** FIXME adapt Injectivity - Element proofs to axiomatic semantics *)

(** FIXME adapt Injectivity - Link proofs to axiomatic semantics *)

