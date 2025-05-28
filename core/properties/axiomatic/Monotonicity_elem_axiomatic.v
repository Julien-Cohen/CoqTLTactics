
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

Require Import core.properties.monotonicity.Moore2Mealy_monotonicity_elem_witness.
Require Import core.properties.monotonicity.sampleMoore_monotonicity_elem.

(*************************************************************)
(** * Monotonicity of Stdlib.L  (element)                       *)
(** * Using axiomatic semantics                              *)
(*************************************************************)

Definition Monotonicity_elem {tc: TransformationConfiguration} 
   (tr: Transformation) :=
forall tr sm1 sm2 rm1 rm2,
  AxiomaticSemantics.is_result tr sm1 rm1 ->
  AxiomaticSemantics.is_result tr sm2 rm2 ->
    incl sm1.(modelElements) sm2.(modelElements) ->
    incl rm1.(modelElements) rm2.(modelElements).

Lemma Moore2Mealy_non_mono_elem_witness:
  exists sm1 sm2 rm1 rm2,
  AxiomaticSemantics.is_result Moore2Mealy sm1 rm1 /\
  AxiomaticSemantics.is_result Moore2Mealy sm2 rm2 /\
    incl sm1.(modelElements) sm2.(modelElements) /\
    ~ (incl rm1.(modelElements) rm2.(modelElements)).
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
        intros.
        destruct H. right. right. left. exact H.
        inversion H.
  simpl.
  unfold not.
  intro.
  apply incl_l_nil in H.
  inversion H.
Qed.

Lemma Moore2Mealy_non_mono_elem : ~ (Monotonicity_elem Moore2Mealy).
Proof.
  unfold Monotonicity_elem.
  intro.
  specialize Moore2Mealy_non_mono_elem_witness ; intro H2.
  destruct H2 as (sm1 & sm2 & rm1 & rm2 & (H3 & H4 & H5 & H6)).
  specialize (H Moore2Mealy sm1 sm2 rm1 rm2 H3 H4 H5).
  contradiction.
Qed.

Theorem non_mono : exists tr, ~ (Monotonicity_elem tr).
Proof.
  exists Moore2Mealy.
  apply Moore2Mealy_non_mono_elem.
Qed.
  
  