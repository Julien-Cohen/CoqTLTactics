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
Require Import AxiomaticSemantics.

(*************************************************************)
(** * Additivity in Rule context (Link)                      *)
(** * Using operational semantics                            *)
(*************************************************************)



Definition Transformation_incl_rules {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (t1.(arity) = t2.(arity)) /\ 
  forall r: Rule, In r t1.(rules) -> In r t2.(rules).

Definition Rule_Additivity_Link {tc: TransformationConfiguration} :=
  forall (t1 t2: Transformation) (sm: SourceModel),
      (Transformation_incl_rules t1 t2 -> 
          incl (execute t1 sm).(modelLinks) (execute t2 sm).(modelLinks)). 

Theorem forall_Additivity_Rules_Link {tc: TransformationConfiguration} : Rule_Additivity_Link.
Proof.
  unfold Rule_Additivity_Link.
  simpl.
  unfold incl.
  unfold compute_trace, produced_elements, applyTrLkOnModel .
  unfold traceTrOnPiece.
  intros ? ? ? ? ?.
  intro.
  apply in_flat_map in H0.
  destruct H0.
  destruct H0.
  apply in_flat_map.
  exists x.
  split.
  + apply in_flat_map.
    apply in_flat_map in H0. destruct H0. exists x0.
    destruct H0.
    unfold allTuples in *.
    split.
    ++ unfold Transformation_incl_rules in H. destruct H. rewrite <- H. assumption.
    ++ apply in_flat_map in H2. destruct H2. destruct H2.
    apply in_flat_map.
    exists x1. split.
    +++ unfold matchingRules in *.
        apply filter_In in H2.
        apply filter_In.
        unfold Transformation_incl_rules in H. destruct H.
        destruct H2.
        specialize (H4 x1 H2).
        split; assumption.
    +++ assumption.
  +
Abort.


(*
  repeat rewrite in_flat_map.
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
      split; assumption.
    + assumption.
Qed.
*)




(**

Definition Transformation_incl_rules'' {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (t1.(arity) = t2.(arity)) /\ 
  subseq t1.(rules) t2.(rules).

Lemma tr_incl_equiv:
  forall (tc: TransformationConfiguration) t1 t2,
    Transformation_incl_rules'' t1 t2 -> Transformation_incl_rules''' t1 t2.
Proof.
intros.
destruct  H.
unfold Transformation_incl_rules'''.
split. 
* assumption.
* intro.
  induction H0.
  + intros.
    contradiction.
  + intros.
    simpl in H1.
    simpl.
    destruct H1.
    - left. assumption.
    - right. auto 2.
  + intros.
    simpl.
    right.
    auto 2.
Qed.

Theorem additivity_rules :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_rules'' t1 t2 -> 
    incl (execute t1 sm).(modelElements)  (execute t2 sm).(modelElements)).
Proof.
 intros.
 specialize (tr_incl_equiv tc t1 t2 H).
 specialize (additivity_rules_general_operational tc t1 t2).
 auto.
Qed.

*)
