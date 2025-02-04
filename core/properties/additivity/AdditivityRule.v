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


(** Deprecated, see below *)
Lemma additivity_rules_general_operational :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_rules''' t1 t2 -> 
    incl  (execute t1 sm).(modelElements)  (execute t2 sm).(modelElements)).
Proof.
  simpl.
  unfold incl.
  unfold compute_trace, produced_elements.
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
      split; assumption.
    + assumption.
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

Require AxiomaticSemantics.

Lemma additivity_rules_general_axiomatic :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_rules''' t1 t2 -> 
  forall rm1 rm2,
  AxiomaticSemantics.is_result t1 sm rm1 ->
  AxiomaticSemantics.is_result t2 sm rm2 ->
    incl  rm1.(modelElements)  rm2.(modelElements)).
Proof.
  unfold AxiomaticSemantics.is_result.
  intros tc t1 t2 sm H rm1 rm2 (H1 & _) (H2 & _).
  unfold incl.
  intros e H_IN.
  specialize (H1 e).
  specialize (H2 e).
  apply H2.
  apply H1 in H_IN.
  clear H1 H2. 
  
  inversion_clear H_IN.
  
  econstructor. 
  (* Show Existentials. *)
  instantiate (2:=a).
  instantiate (1:=c).

  unfold Transformation_incl_rules''' in H.
  destruct H as (H1 & H2).

  inversion_clear H0.
  econstructor.
  instantiate (1:=sp).

  3:{ congruence. }
  
  2:{ assumption. }

  inversion_clear H.
  econstructor.
  instantiate (1:=r).
  
  assumption.  
  inversion_clear H5.
  constructor ; auto.
 
Qed.

Lemma additivity_rules_general_second_proof :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_rules''' t1 t2 -> 
    incl  (execute t1 sm).(modelElements)  (execute t2 sm).(modelElements)).
Proof.
  intros. 
  apply additivity_rules_general_axiomatic with (t1:=t1) (t2:=t2) (sm:=sm) ; [ assumption | | ].
  + apply AxiomaticSemantics.prop13.
  + apply AxiomaticSemantics.prop13.
Qed.

