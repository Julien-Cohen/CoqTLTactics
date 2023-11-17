Require Moore2MealyALT.MooreSemantics.
Require Moore2MealyALT.MealySemantics.
Require Moore2MealyALT.Moore2Mealy.
Require Moore2MealyALT.MooreWF.
Require Moore2MealyALT.MealyWF.
Require Moore2MealyALT.theorems.Elements.
Require Moore2MealyALT.theorems.WFStable.
Require Moore2MealyALT.theorems.InitStable.
Require Moore2MealyALT.theorems.StepCommut.

Import String OptionUtils.

Section Foo.

Variable (m:Moore.M).

Hypothesis WF_S : Moore.WF_source m.
Hypothesis WF_T : Moore.WF_target m.
Hypothesis WF_D : MooreWF.determinist m.
Hypothesis WF_U : MooreWF.unique_ids m.


Lemma star_step_commut_fw :
  forall i s r,
    MooreSemantics.executeFromState m s i = Some r ->
    MealySemantics.executeFromState
      (Semantics.execute Moore2Mealy.Moore2Mealy m)
      (Elements.convert_state s) i = Some r.
Proof.
  induction i ; simpl ; intros s r STEP ; [ congruence | ].
  rename s into s1.
  PropUtils.destruct_match_H STEP ; [ | discriminate ].
  rename s into s2.
  PropUtils.destruct_match_H STEP ; [ | discriminate ].
  PropUtils.inj STEP.
  apply StepCommut.search_commut_fw in Heqo ; auto. 
  destruct Heqo as (s1' & s2' & ? & ? & t' & ? & ?).
  rewrite <- H.
  rewrite H1.
  specialize (IHi s2 l Heqo0).
  rewrite <- H0 in IHi.
  rewrite IHi.
  f_equal.
  f_equal.
  assumption.
Qed.


Lemma star_step_commut_bw :
  forall i s' r,
    MealySemantics.executeFromState
      (Semantics.execute Moore2Mealy.Moore2Mealy m)
      s' i = Some r -> 
    ( i= nil /\ r = nil ) \/
    exists s, 
      s'= Elements.convert_state s /\ List.In (Moore.StateElement s) m.(Model.modelElements) /\ MooreSemantics.executeFromState m s i = Some r.
Proof.
  induction i ; intros s r STEP.
  { 
    simpl in STEP.
    PropUtils.inj STEP.
    left.
    auto.
  }
  {
    right.
    rename s into s1'.
    assert (List.In (Mealy.StateElement s1') (Semantics.execute Moore2Mealy.Moore2Mealy m).(Model.modelElements)).
    { apply MealySemantics.execute_in in STEP ; auto. discriminate. }
    
    simpl in STEP. simpl.
    PropUtils.destruct_match_H STEP ; [ | discriminate ].
    destruct p.
    rename s into s2'.
    PropUtils.destruct_match_H STEP ; [ | discriminate ].
    PropUtils.inj STEP.
    apply StepCommut.search_commut_bw in Heqo ; auto.
    destruct Heqo as (s1 & ? & s2 & ? & ? & ?).
    apply Elements.state_element_bw in H.
    destruct H as (s1_alt & ? & ?).
    
    assert (s1_alt = s1).
    { 
      eapply Elements.convert_state_injective ; eauto.
      { eapply MooreSemantics.search_in_left ; eauto. }
      { congruence. }
    }
    subst s1_alt.
    
    exists s1.
    split ; [ assumption | ].
    rewrite H2. 
    split ; [ assumption | ].
    specialize (IHi s2' l Heqo0).
    destruct IHi.
    { 
      destruct H5 ; subst. simpl.
      congruence.
    }
    destruct H5 as (s2_alt & ? & ? & ?).
    assert (s2_alt = s2).
    {
      eapply Elements.convert_state_injective ; eauto.
      eapply MooreSemantics.search_in_right ; eauto.
      congruence.
    }
    subst s2_alt.
    rewrite H7.
    f_equal.
    f_equal.
    auto.
  }
Qed.

Lemma SemanticsPreservation :
  forall i,
    MealySemantics.execute (Semantics.execute Moore2Mealy.Moore2Mealy m) i = MooreSemantics.execute m i.
Proof. 

  unfold MealySemantics.execute.
  unfold MooreSemantics.execute.
  
  intro i .
  destruct (MooreSemantics.initialState m) eqn:INIT.
  2:{ 
    apply InitStable.initial_state_preserved_fw3 in INIT.
    rewrite INIT.
    reflexivity.
  }    

  {
    cut (List.In (Moore.StateElement s) m.(Model.modelElements)).
    {
      intro IN.
      apply InitStable.initial_state_preserved_fw2 in INIT. 
      rewrite INIT.
      
      clear INIT.
      match goal with [ |- ?A = ?B] => destruct B eqn:? end. 
      
      + apply star_step_commut_fw in Heqo ; auto.
      + destruct i.
        simpl in *.
        auto.
        match goal with [ |- ?A = None ] => destruct A eqn:? end ; [ exfalso | reflexivity ].   
        apply star_step_commut_bw in Heqo0 ; auto.
        destruct Heqo0.
        destruct H ; discriminate. 
        destruct H as (? & ? & ? & ?).
        eapply Elements.convert_state_injective in H ; eauto.
        subst x.
        congruence.
    }
    {
      (* inversion *)
      unfold MooreSemantics.initialState in INIT.
      apply OptionListUtils.find_lift_some in INIT.
      destruct INIT as (?&?&?&?).
      unfold Moore.get_E_data in H ; simpl in H. destruct x ; [ PropUtils.inj H | discriminate H].
      assumption.
    }
  }
Qed.

End Foo.
