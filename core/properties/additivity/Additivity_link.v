Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
From Stdlib Require Import String.
From Stdlib Require Import EqNat.
From Stdlib Require Import List.
Require Import core.utils.Utils.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.
Require Import AxiomaticSemantics.


Require Import core.properties.additivity.Moore2Mealy_Additivity_link_witness.
Require Import core.properties.additivity.sampleMoore_additivity_link.


(*************************************************************)
(** * Additivity in Rule context (Link)                      *)
(** * Using operational semantics                            *)
(*************************************************************)

From Stdlib Require Import Logic.Classical_Pred_Type.

Require RuleIncl.

Definition Rule_Additivity_Link {tc: TransformationConfiguration} :=
  forall (t1 t2: Transformation) (sm: SourceModel),
      (RuleIncl.Transformation_incl_rules t1 t2 -> 
          incl (execute t1 sm).(modelLinks) (execute t2 sm).(modelLinks)). 

Lemma Moore2Mealy_non_additivity_link_contrapos:
  exists sm : SourceModel,
  ~
  (RuleIncl.Transformation_incl_rules Moore2Mealy_t1
    Moore2Mealy_t2 ->
  incl (modelLinks (execute Moore2Mealy_t1 sm))
    (modelLinks (execute Moore2Mealy_t2 sm))).
Proof.
  exists Moore_m.
  unfold not.
  intro.
  assert (RuleIncl.Transformation_incl_rules Moore2Mealy_t1 Moore2Mealy_t2).
  {
    unfold Moore2Mealy_t1. unfold Moore2Mealy_t2.
    unfold RuleIncl.Transformation_incl_rules.
    simpl.
    crush.
  }
  specialize (H H0).
  clear H0.
  unfold not.
  unfold incl in H.
  simpl in H.
  apply ex_not_not_all in H.
  assumption.
  compute.
  eexists.
  intro.
  destruct H0.
  ++ left.
     reflexivity.
  ++ crush.
  ++ assumption.
Qed.

Lemma not_additivity_link : ~ (Rule_Additivity_Link).
Proof.
  unfold Rule_Additivity_Link.
  apply ex_not_not_all.
  exists Moore2Mealy_t1.
  apply ex_not_not_all.
  exists Moore2Mealy_t2.
  apply ex_not_not_all.
  apply Moore2Mealy_non_additivity_link_contrapos.
Qed.





