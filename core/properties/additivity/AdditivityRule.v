Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.


(*************************************************************)
(** * Additivity in Rule context                             *)
(*************************************************************)

Definition Transformation_incl_rules'' {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (t1.(arity) = t2.(arity)) /\ 
  subseq t1.(rules) t2.(rules).


Definition Transformation_incl_rules''' {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (t1.(arity) = t2.(arity)) /\ 
  forall r: Rule, In r t1.(rules) -> In r t2.(rules).


Lemma tr_incl_equiv:
  forall (tc: TransformationConfiguration) t1 t2,
    Transformation_incl_rules'' t1 t2 -> Transformation_incl_rules''' t1 t2.
Proof.
intros.
destruct  H.
unfold Transformation_incl_rules'''.
split. 
* auto.
* intro.
  induction H0.
  + intros.
    contradiction.
  + intros.
    simpl in H1.
    simpl.
    destruct H1.
    - left. crush.
    - right. crush.
  + intros.
    simpl.
    right.
    auto.
Qed.



Lemma additivity_rules_general :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_rules''' t1 t2 -> 
    incl  (execute t1 sm).(modelElements)  (execute t2 sm).(modelElements)).
Proof.
  simpl.
  unfold incl.
  unfold instantiateTrOnModel.
  unfold traceTrOnModel.
  unfold traceTrOnPiece.
  intros ? ? ? ? ? ?.
  repeat rewrite map_flat_map.
  intro H0.
  apply in_flat_map in H0. destruct H0 as (r1, (H0, H1)). 
  rewrite map_flat_map in H1.
  apply in_flat_map in H1. destruct H1 as (r2, (H1,H2)).
  apply filter_In in H1. destruct H1.
  destruct H as (H4, H5).
  apply in_flat_map. exists r1.
  split.
  * unfold allTuples.
    rewrite <- H4.
    assumption.
  * rewrite map_flat_map.
    apply in_flat_map.
    specialize (H5 r2 H1).
    exists r2.
    split.
    + apply filter_In.
      split; auto.
    + auto.
Qed.

Theorem additivity_rules :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_rules'' t1 t2 -> 
    incl (execute t1 sm).(modelElements)  (execute t2 sm).(modelElements)).
Proof.
intros.
specialize (tr_incl_equiv tc t1 t2 H).
specialize (additivity_rules_general tc t1 t2).
auto.
Qed.
