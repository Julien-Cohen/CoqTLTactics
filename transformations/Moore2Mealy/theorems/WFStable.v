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

Lemma transition_source_uniqueness_stable :
  forall m,
    Moore.WF_transition_source_exists m -> 
    MooreWF.WF_transition_source_uniqueness m -> 
    MealyWF.WF_transition_source_uniqueness (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intros m  WF2 WF4.
  unfold MealyWF.WF_transition_source_uniqueness.
  intros. 

  destruct lk1 as (t' & s').
  destruct lk2 as (t'' & s'').
  simpl in H1. subst t''.
  f_equal.
  
  destruct (Links.source_link_bw _ WF2 _ _ H) as (s1 & C1 & IN1).
  destruct (Links.source_link_bw _ WF2 _ _ H0) as (s2 & C2 & IN2).

  specialize (WF4 _ _ IN1 IN2 (eq_refl _)). 
  PropUtils.inj WF4.
  reflexivity.
Qed.

Lemma transition_target_uniqueness_stable :
  forall m,
    MooreWF.WF_transition_target_uniqueness m -> 
    MealyWF.WF_transition_target_uniqueness (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intros m WF4.
  unfold MealyWF.WF_transition_target_uniqueness.
  intros. 

  destruct lk1 as (t' & s').
  destruct lk2 as (t'' & s'').
  simpl in H1. subst t''.
  f_equal.
  
  destruct (Links.target_link_bw _ _ _ H) as (s1 & C1 & IN1).
  destruct (Links.target_link_bw _ _ _ H0) as (s2 & C2 & IN2).

  specialize (WF4 _ _ IN1 IN2 (eq_refl _)). 
  PropUtils.inj WF4.
  reflexivity.
Qed.

#[global]
Hint Resolve transition_source_uniqueness_stable transition_target_uniqueness_stable : wf.

Lemma transition_target_glue_r_exists_stable m :
  Moore.WF_transition_target_glue_r_exists m ->
  Mealy.WF_transition_target_glue_r_exists (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  unfold 
    Moore.WF_transition_target_glue_r_exists, 
    Mealy.WF_transition_target_glue_r_exists.
  intros WF_MOORE t IN_MEALY.

  destruct t.
  apply Links.target_link_bw in IN_MEALY.
  destruct IN_MEALY as (s0 & C & IN_MOORE).
  unfold Glue.trg.
  apply WF_MOORE in IN_MOORE.
  unfold Glue.trg in IN_MOORE.
  apply Elements.state_element_fw in IN_MOORE.
  rewrite C in IN_MOORE.
  exact IN_MOORE.
Qed.
