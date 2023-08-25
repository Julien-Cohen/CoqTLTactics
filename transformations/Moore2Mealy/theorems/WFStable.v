Require Moore2Mealy.MooreSemantics.
Require Moore2Mealy.MealySemantics.
Require Moore2Mealy.Moore2Mealy.
Require Moore2Mealy.MooreWF.
Require Moore2Mealy.MealyWF.
Require Moore2Mealy.theorems.Elements.
Require Moore2Mealy.theorems.Links.

Import String.

Lemma state_id_uniqueness_preserved_fw : forall m,
    MooreWF.state_id_uniqueness m -> 
    MealyWF.state_id_uniqueness (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intros ; apply MealyWF.always_state_id_uniqueness.
Qed.

Import Model Semantics.

Lemma WF_transition_source_uniqueness_stable :
  forall m,
    Moore.WF_transition_target_exists m ->
    Moore.WF_transition_source_exists m -> 
    MooreWF.WF_transition_source_uniqueness m -> 
    MealyWF.WF_transition_source_uniqueness (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intros m WF1 WF2 WF4.
  unfold MealyWF.WF_transition_source_uniqueness.
  intros. 

  destruct lk1 as (t' & s').
  destruct lk2 as (t'' & s'').
  simpl in H1. subst t''.
  f_equal.
  
  destruct (Links.source_link_bw _ WF1 WF2 _ _ H) as (s1 & C1 & IN1).
  destruct (Links.source_link_bw _ WF1 WF2 _ _ H0) as (s2 & C2 & IN2).

  specialize (WF4 _ _ IN1 IN2 (eq_refl _)). 
  PropUtils.inj WF4.
  reflexivity.
Qed.

#[global]
Hint Resolve WF_transition_source_uniqueness_stable : fw.
