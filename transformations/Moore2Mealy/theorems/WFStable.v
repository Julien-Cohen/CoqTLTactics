From transformations.Moore2Mealy
  Require MooreSemantics MealySemantics Moore2Mealy MooreWF MealyWF Elements Links.

Import String Model Semantics.


Lemma state_id_uniqueness_preserved_fw : forall m,
    MooreWF.state_id_uniqueness m -> 
    MealyWF.state_id_uniqueness (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intros ; apply MealyWF.always_state_id_uniqueness.
Qed.



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


Lemma transition_source_glue_r_exists_stable m :
  Moore.WF_transition_source_exists m ->
  Moore.WF_transition_source_glue_r_exists m ->
  Mealy.WF_transition_source_glue_r_exists (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intro WF0.
  unfold 
    Moore.WF_transition_source_glue_r_exists, 
    Mealy.WF_transition_source_glue_r_exists.
  intros WF_MOORE t IN_MEALY.

  destruct t.
  apply Links.source_link_bw in IN_MEALY ; auto.
  destruct IN_MEALY as (s0 & C & IN_MOORE).
  unfold Glue.trg.
  apply WF_MOORE in IN_MOORE.
  unfold Glue.trg in IN_MOORE.
  apply Elements.state_element_fw in IN_MOORE.
  rewrite C in IN_MOORE.
  exact IN_MOORE.
Qed.


Lemma WF_target_stable m:
  MooreWF.WF_transition_target_uniqueness m ->
  Moore.WF_transition_target_glue_r_exists m ->
  Moore.WF_transition_target_glue_l_exists m ->
  Moore.WF_transition_target_exists m ->
  Mealy.WF_transition_target_exists (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intros WF0 WF1 WF2.
  unfold 
    Moore.WF_transition_target_exists,
    Mealy.WF_transition_target_exists.
  intro WF.
  intros t IN_MEALY.
  apply Elements.transition_element_bw in IN_MEALY.
  destruct IN_MEALY as (t0 & IN_MOORE & C).
  apply WF in IN_MOORE.
  destruct IN_MOORE as (s0 & G).
  apply Moore.getTransition_target_inv in G.
  apply Links.target_link_fw in G ; auto.
  destruct G as (t' & C' & IN_MEALY).
  rewrite C' in C.
  PropUtils.inj C.
  exists (Moore2Mealy.convert_state s0).
  apply MealyWF.getTransition_target_some ; auto with wf ; [].
  apply transition_target_glue_r_exists_stable in WF1.
  apply WF1 in IN_MEALY.
  exact IN_MEALY.
Qed.


#[global]
Hint Resolve transition_target_glue_r_exists_stable transition_source_glue_r_exists_stable WF_target_stable : wf.


Lemma determinist_stable m :
  Moore.WF_transition_target_exists m ->
  Moore.WF_transition_source_glue_r_exists m ->
  MooreWF.state_id_uniqueness m ->
  Moore.WF_transition_source_exists m ->
  MooreWF.WF_transition_source_uniqueness m ->
  MooreWF.determinist m ->
  MealyWF.determinist (Semantics.execute  Moore2Mealy.Moore2Mealy m).
Proof.
  intros WF_1 WF_3 WF_4 WF_5 WF_6 WF_2.
  unfold MealyWF.determinist.
  intros s t1 t2 H1 H2 H4.
  apply MealySemantics.State_out_transitions_inv in H1.
  apply MealySemantics.State_out_transitions_inv in H2.
  destruct H1 as (IN1 & G1).
  destruct H2 as (IN2 & G2).
  
  apply Elements.transition_element_bw in IN1. 
  apply Elements.transition_element_bw in IN2.
  destruct IN1 as (mt1 & ? & ?).
  destruct IN2 as (mt2 & ? & ?).
  unfold Moore2Mealy.convert_transition in H0.
  PropUtils.destruct_match_H H0 ; [ PropUtils.inj H0 | discriminate H0 ] ; simpl in *.
  unfold Moore2Mealy.convert_transition in H2.
  PropUtils.destruct_match_H H2 ; [ PropUtils.inj H2 | discriminate H2 ] ; simpl in *.

  apply Mealy.getTransition_source_inv in G1.
  apply Mealy.getTransition_source_inv in G2.
  
  apply Links.source_link_bw in G1 ; auto ; [].
  apply Links.source_link_bw in G2 ; auto ; [].
  simpl in G1, G2.
  destruct G1 as (s01 & C1 & IN1).

  destruct G2 as (s02 & C2 & IN2).

  PropUtils.duplicate IN1 IN_S01.
  apply WF_3 in IN_S01. simpl in IN_S01.

  PropUtils.duplicate IN2 IN_S02.
  apply WF_3 in IN_S02. simpl in IN_S02.


  assert (s01 = s02). 
  { eapply Elements.convert_state_injective ; eauto. 
    congruence.
  }
  subst s02.
  clear IN_S02.

  assert (mt1 = mt2).
  {
    unfold MooreWF.determinist in WF_2.

    eapply WF_2 ; eauto ; [ | ].

    + apply MooreSemantics.in_State_outTransitions ; auto.
      (* We would like to have GettersCommut. *)
      apply MooreWF.getTransition_source_some ; eauto.
      destruct mt1 ; exact IN1.
    + apply MooreSemantics.in_State_outTransitions ; auto.
      apply MooreWF.getTransition_source_some ; eauto.
      destruct mt2 ; exact IN2.
  }

  subst mt2.
  congruence.
Qed.


#[global]
Hint Resolve determinist_stable : wf.
