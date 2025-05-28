
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
Require Import core.utils.Utils.
Require Import core.AxiomaticSemantics.

Require Import core.properties.monotonicity.Moore2Mealy_monotonicity_link_witness.
Require Import core.properties.monotonicity.sampleMoore_monotonicity_link.

(*************************************************************)
(** * Monotonicity of Stdlib.L (link)                           *)
(** * Using axiomatic semantics                              *)
(*************************************************************)

Definition Monotonicity_link {tc: TransformationConfiguration} 
   (tr: Transformation) :=
forall tr sm1 sm2 rm1 rm2,
  AxiomaticSemantics.is_result tr sm1 rm1 ->
  AxiomaticSemantics.is_result tr sm2 rm2 ->
    incl sm1.(modelLinks) sm2.(modelLinks) ->
    incl rm1.(modelLinks) rm2.(modelLinks).

Lemma Moore2Mealy_non_mono_link_witness:
    exists sm1 sm2 rm1 rm2,
    AxiomaticSemantics.is_result Moore2Mealy sm1 rm1 /\
    AxiomaticSemantics.is_result Moore2Mealy sm2 rm2 /\
      incl sm1.(modelLinks) sm2.(modelLinks) /\
      ~ (incl rm1.(modelLinks) rm2.(modelLinks)).
Proof.
  exists Moore_m1.
  exists Moore_m2.
  exists (execute Moore2Mealy Moore_m1).
  exists (execute Moore2Mealy Moore_m2).
  split.
  - apply AxiomaticSemantics.prop13.
  - split. apply AxiomaticSemantics.prop13.
    --  split. 
        unfold incl.
        simpl.
        crush.
  simpl.
  unfold not.
  intro.
  apply incl_l_nil in H.
  inversion H.
Qed.

Lemma Moore2Mealy_non_mono_link : ~ (Monotonicity_link Moore2Mealy).
Proof.
  unfold Monotonicity_link.
  intro.
  specialize Moore2Mealy_non_mono_link_witness as witness.
  destruct witness.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H2.
  specialize (H Moore2Mealy x x0 x1 x2 H0 H1 H2).
  contradiction.
Qed.

Theorem non_mono_link  :
  exists tr, ~ (Monotonicity_link tr).
Proof.
  exists Moore2Mealy.
  apply Moore2Mealy_non_mono_link.
Qed.

  