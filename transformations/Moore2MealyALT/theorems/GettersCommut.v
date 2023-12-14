Require Moore2MealyALT.MooreSemantics.
Require Moore2MealyALT.MealySemantics.
Require Moore2MealyALT.Moore2Mealy.
Require Moore2MealyALT.MooreWF.
Require Moore2MealyALT.MealyWF.
Require Moore2MealyALT.theorems.Elements.
Require Moore2MealyALT.theorems.WFStable.

Import String.

Section Foo.

Variable (m:Moore.M).

Hypothesis WF_S : Moore.WF_source m.
Hypothesis WF_T : Moore.WF_target m.

Lemma getTransition_source_commut_fw t :
  forall s t',
      Moore.getTransition_source m t = Some s ->
      Elements.convert_transition m t = Some t' ->
      Mealy.getTransition_source (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some (Elements.convert_state s).
Proof.
  intros.
  destruct (Moore.getTransition_source_inv _ _ _ H).

  apply MealyWF.getTransition_source_some.
  { apply MealyWF.always_unique_ids. }
  { apply Elements.state_element_fw. assumption. }
  { 
    destruct (Elements.convert_transition_nec _ _ _ H0) as (?&?&?) ;
      subst.
    unfold Elements.convert_state.
    simpl.
    auto.
  }
Qed.

Lemma getTransition_source_commut_bw t :
  forall s t',
      Mealy.getTransition_source (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some (Elements.convert_state s) ->
      Elements.convert_transition m t = Some t' ->
      exists s', s'.(Moore.State_id) = s.(Moore.State_id) /\ 
      Moore.getTransition_source m t = Some s'. (* weak result because convert_state is not injective *)
Proof.
  intros.
  destruct (Mealy.getTransition_source_inv _ _ _ H).
  destruct (Elements.state_element_bw _ _ H1) as (?&?&?).
  unfold Elements.convert_state in H4.
  PropUtils.inj H4.

  unfold Moore.getTransition_source.
  unfold OptionListUtils.find_lift.

  destruct (Elements.convert_transition_nec _ _  _ H0) as  (s0 & Heqo & E) ; subst t'.

  simpl in H2.
  
  cut (exists s' : Moore.State_t,
    List.find
      (fun s0 : Moore.getTypeByEKind Moore.State_K =>
       Id.NodeId_beq (Moore.Transition_source t) (Moore.State_id s0))
      (OptionListUtils.lift_list (Moore.get_E_data Moore.State_K)
         (Model.modelElements m)) = Some s').
  { 
    intros (s2&?). exists s2.
    destruct (List.find_some _ _ H5).
    split ; auto.
    apply Id.internal_NodeId_dec_bl in H7.
    rewrite <- H2.
    rewrite <- H7.
    reflexivity.
  }
  {
    eapply ListUtils.find_some_left.
    apply Moore.In_state. 
    eassumption.
    apply Id.internal_NodeId_dec_lb.
    congruence.
  }
Qed.

(* FIXME : this should be the main bw lemma *)
Corollary getTransition_source_commut_bw_alt t :
  forall s' t',
      Mealy.getTransition_source (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some s' ->
      Elements.convert_transition m t = Some t' ->
      exists s, s' = Elements.convert_state s /\ 
                  Moore.getTransition_source m t = Some s. (* weak result because convert_state is not injective *)
Proof.
  intros.
  replace s' with (Elements.convert_state (Moore.Build_State_t s'.(Mealy.State_id) ""%string)) in H.
  { 
    eapply getTransition_source_commut_bw in H ; eauto.
    destruct H as (?&?&?).
    eexists ; split ; eauto.
    unfold Elements.convert_state.
    destruct x ; destruct s' ; simpl in * ; congruence.
  }
  { destruct s' ; reflexivity. }
Qed.


(** [getTransition_target] *)

Lemma getTransition_target_commut_fw t :
  forall s,
      Moore.getTransition_target m t = Some s ->
      let t' := {|
        Mealy.Transition_source := Moore.Transition_source t;
        Mealy.Transition_input := Moore.Transition_input t;
        Mealy.Transition_output := Moore.State_output s;
        Mealy.Transition_dest := Moore.Transition_dest t
      |} in 
      Elements.convert_transition m t = Some t' /\ 
      Mealy.getTransition_target (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some (Elements.convert_state s).
Proof.
  intros.
  unfold Elements.convert_transition.
  rewrite H.
  split ; [ subst t' ; reflexivity | ].
  destruct (Moore.getTransition_target_inv _ _ _ H).

  apply MealyWF.getTransition_target_some.
  { apply MealyWF.always_unique_ids. }
  { apply Elements.state_element_fw. assumption. }
  { unfold Elements.convert_state ; simpl. auto. }
Qed.


Lemma getTransition_target_commut_bw :
  forall s' t',
    List.In (Mealy.TransitionElement t') (Semantics.execute Moore2Mealy.Moore2Mealy m).(Model.modelElements) ->  
      Mealy.getTransition_target (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some s' ->
      exists t,
      Elements.convert_transition m t = Some t' /\
      exists s, s' = Elements.convert_state s /\ 
      Moore.getTransition_target m t = Some s. 
Proof.
  intros.
  destruct (Mealy.getTransition_target_inv _ _ _ H0).
  destruct (Elements.state_element_bw _ _ H1) as (s&?&?).
  destruct (Elements.transition_element_bw _ _ H) as (t&?&?).

  exists t.
  split ; auto.
  apply eq_sym in H6.
  destruct (Elements.convert_transition_nec _ _ _ H6) as (s2&?&?) ; subst t'.
  exists s2.
  split ; auto.
  simpl in H2.
  destruct s', s2.
  unfold Elements.convert_state.
  f_equal. simpl.
  destruct (Moore.getTransition_target_inv _ _ _ H7). simpl in H9.
  clear H7.
  simpl in H2.
  congruence.
Qed.

End Foo.
