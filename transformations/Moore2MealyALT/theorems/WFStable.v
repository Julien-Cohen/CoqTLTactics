Require Moore2MealyALT.MooreSemantics.
Require Moore2MealyALT.MealySemantics.
Require Moore2MealyALT.Moore2Mealy.
Require Moore2MealyALT.MooreWF.
Require Moore2MealyALT.MealyWF.
Require Moore2MealyALT.theorems.Elements.


Lemma determinist_preserved m :
  Moore.WF1 m ->
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
  PropUtils.destruct_match H0 ; [ PropUtils.inj H0 | discriminate H0 ] ; simpl in *.
  unfold Elements.convert_transition in H2.
  PropUtils.destruct_match H2 ; [ PropUtils.inj H2 | discriminate H2 ] ; simpl in *.
  specialize (WF_2 H3 H4).
  subst.
  rewrite Heqo in Heqo0 ; PropUtils.inj Heqo0. (* auto_unif *)
  reflexivity.
Qed.


Lemma unique_names_preserved_fw : forall m,
    MooreWF.unique_names m -> 
    MealyWF.unique_names (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intros ; apply MealyWF.always_unique_names.
Qed.
