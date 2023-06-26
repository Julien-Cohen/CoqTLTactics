Require Moore2MealyALT.MooreSemantics.
Require Moore2MealyALT.MealySemantics.
Require Moore2MealyALT.Moore2Mealy.
Require Moore2MealyALT.MooreWF.
Require Moore2MealyALT.MealyWF.
Require Moore2MealyALT.theorems.Elements.
Require Moore2MealyALT.theorems.WFStable.
Require Moore2MealyALT.theorems.InitStable.

Import String OptionUtils.

Lemma getTransition_source_stable m t :
  Moore.WF_source m ->
  forall s t',
      Moore.getTransition_source m t = Some s ->
      Elements.convert_transition m t = Some t' ->
      Mealy.getTransition_source
        (Semantics.execute Moore2Mealy.Moore2Mealy m)
        t' = Some (Elements.convert s).
Proof.
  intros.
  apply Moore.getTransition_source_inv in H0.
  destruct H0.

  apply MealyWF.getTransition_source_some.
  { apply MealyWF.always_unique_ids. }
  { apply Elements.state_element_fw. assumption. }
  { 
    apply Elements.convert_transition_inv in H1.
    destruct H1 as (?&?&?) ; subst.
    unfold Elements.convert.
    simpl.
    auto.
  }
Qed.

Lemma State_out_transitions_inv m s t :
  List.In t (MooreSemantics.State_outTransitions m s) ->
  List.In (Moore.TransitionElement t) (Model.modelElements m)
  /\ Moore.getTransition_source m t = Some s.
Proof.
  intro H.
  unfold MooreSemantics.State_outTransitions in H.
  apply OptionListUtils.filter_lift_in in H.
  destruct H as (? & ? & ? & ?).                   
  PropUtils.destruct_match H1 ; [ | discriminate H1]. 
  apply Moore.lem_State_t_beq_id in H1. subst s0.    
  destruct x ; unfold Moore.get_E_data in H0 ; [discriminate H0 | PropUtils.inj H0]. (* monadInv *) 
  auto.
Qed.

Lemma State_acceptTransition_some :
  forall t s i r,
    MealyWF.determinist t ->
    r.(Mealy.Transition_input) = i ->
    List.In r (MealySemantics.State_outTransitions t s) ->
    MealySemantics.State_acceptTransition t s i = Some r.
Proof.
  intros.
  unfold MealySemantics.State_acceptTransition.
  apply ListUtils.in_find.
  { apply MealyWF.truc. assumption. }
  { apply String.eqb_eq. auto. }
  { assumption. }
Qed.

Lemma in_State_outTransitions (m:Mealy.M) s t :
  List.In (Mealy.TransitionElement t) (Model.modelElements m) ->
  Mealy.getTransition_source m t = Some s ->
  List.In t (MealySemantics.State_outTransitions m s).
Proof.
  intros.
  unfold MealySemantics.State_outTransitions.
  apply OptionListUtils.filter_lift_in.
  exists (Mealy.TransitionElement t).
  split ; [ assumption | ].
  split ; [ reflexivity | ].
  rewrite H0.
  apply Mealy.internal_State_t_dec_lb.
  reflexivity.
Qed.



Lemma State_acceptTransition_eq :
  forall s m i t,
    Moore.WF_source m ->
    Moore.WF_target m ->
    MooreWF.determinist m ->
    MooreSemantics.State_acceptTransition m s i = Some t ->
    MealySemantics.State_acceptTransition (Semantics.execute Moore2Mealy.Moore2Mealy m) (Elements.convert s) i = Elements.convert_transition m t.
Proof.
  intros s m i t WF_1 WF_2 WF_3 A.

  unfold MooreSemantics.State_acceptTransition in A.
  apply List.find_some in A. destruct A as [H1 H2].
  apply State_out_transitions_inv in H1 ; destruct H1.
  

  apply String.eqb_eq in H2. subst.

  unfold Elements.convert_transition.
  destruct ( WF_2  _ H) as (s' & H4).
  rewrite H4.
  apply State_acceptTransition_some.
    { apply WFStable.determinist_preserved ; assumption. }
    { reflexivity. }
    { 
      apply Elements.transition_element_fw in H ; auto.
        destruct H as (?&?&?).
        apply Elements.convert_transition_inv in H.
        destruct H as (?&?&?). subst.
        rewrite H in H4 ; PropUtils.inj H4. (* unif *)

        apply in_State_outTransitions.
      { assumption.    }        
      { 
        eapply getTransition_source_stable ; eauto.
        unfold Elements.convert_transition.
        rewrite H.
        reflexivity.
      }
    }
Qed.
