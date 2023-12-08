Require Moore2MealyALT.MooreSemantics.
Require Moore2MealyALT.MealySemantics.
Require Moore2MealyALT.Moore2Mealy.
Require Moore2MealyALT.MooreWF.
Require Moore2MealyALT.MealyWF.
Require Moore2MealyALT.theorems.Elements.


Lemma determinist_stable m :
  Moore.WF_target m ->
  MooreWF.determinist m ->
  MealyWF.determinist (Semantics.execute  Moore2Mealy.Moore2Mealy m).
Proof.
  intros WF_1 WF_2.
  unfold MealyWF.determinist.
  intros t1 t2 H1 H2 H3 H4.
  apply Elements.transition_element_bw in H1 ; auto.
  apply Elements.transition_element_bw in H2 ; auto.
  destruct H1 as (mt1 & ? & ?).
  destruct H2 as (mt2 & ? & ?).
  specialize (WF_2 mt1 mt2 H H1).
  unfold Elements.convert_transition in H0.
  PropUtils.destruct_match_H H0 ; [ PropUtils.inj H0 | discriminate H0 ] ; simpl in *.
  unfold Elements.convert_transition in H2.
  PropUtils.destruct_match_H H2 ; [ PropUtils.inj H2 | discriminate H2 ] ; simpl in *.
  specialize (WF_2 H3 H4).
  subst.
  PropUtils.unif Heqo Heqo0. (* auto_unif *)
  reflexivity.
Qed.

#[global]
Hint Resolve determinist_stable : wf.


Lemma unique_ids_preserved_fw : forall m,
    MooreWF.unique_ids m -> 
    MealyWF.unique_ids (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intros ; apply MealyWF.always_unique_ids.
Qed.

Lemma WF_source_stable : 
  forall m,
    Moore.WF_target m ->
    Moore.WF_source m ->
    Mealy.WF_source (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intros m WF_1 WF_2. 
  intros t H.
  apply Elements.transition_element_bw in H ; auto.
  destruct H as ( t0 & ? & ?).
  unfold Elements.convert_transition in H0.
  PropUtils.destruct_match_H H0 ; [ PropUtils.inj H0 | discriminate H0].
  destruct (WF_2 _ H) as (s0 & G).
  clear Heqo.
  exists (Elements.convert_state s0).

  apply Moore.getTransition_source_inv in G.
  destruct G.
  apply MealyWF.getTransition_source_some.
  { apply MealyWF.always_unique_ids. }
  { apply Elements.state_element_fw. assumption. }
  { unfold Mealy.Transition_source.
    unfold Elements.convert_state.
    auto.
  }
Qed.

#[global]
Hint Resolve WF_source_stable : wf.

Lemma WF_target_stable : (* same proof *) 
  forall m,
    Moore.WF_target m ->
    Mealy.WF_target (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intros m WF_1. 
  intros t H.
  apply Elements.transition_element_bw in H ; auto.
  destruct H as ( t0 & ? & ?).
  unfold Elements.convert_transition in H0.
  PropUtils.destruct_match_H H0 ; [ PropUtils.inj H0 | discriminate H0].
  destruct (WF_1 _ H) as (s0 & G).
  clear Heqo.
  exists (Elements.convert_state s0).

  apply Moore.getTransition_target_inv in G.
  destruct G.
  apply MealyWF.getTransition_target_some.
  { apply MealyWF.always_unique_ids. }
  { apply Elements.state_element_fw. assumption. }
  { 
    unfold Mealy.Transition_dest.
    unfold Elements.convert_state.
    auto.
  }
Qed.

#[global]
Hint Resolve WF_target_stable : wf.
