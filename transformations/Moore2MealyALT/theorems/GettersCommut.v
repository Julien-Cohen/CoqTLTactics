Require Moore2MealyALT.MooreSemantics.
Require Moore2MealyALT.MealySemantics.
Require Moore2MealyALT.Moore2Mealy.
Require Moore2MealyALT.MooreWF.
Require Moore2MealyALT.MealyWF.
Require Moore2MealyALT.theorems.Elements.
Require Moore2MealyALT.theorems.WFStable.

Import String.

Lemma getTransition_source_commut_fw m t :
  Moore.WF_source m ->
  forall s t',
      Moore.getTransition_source m t = Some s ->
      Elements.convert_transition m t = Some t' ->
      Mealy.getTransition_source (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some (Elements.convert s).
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

Lemma getTransition_source_commut_none_fw m t :
  Moore.WF_source m ->
  forall  t',
      Moore.getTransition_source m t = None ->
      Elements.convert_transition m t = Some t' ->
      Mealy.getTransition_source (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = None.
Proof.
  intros.
  unfold Moore.getTransition_source in H0.
  unfold Mealy.getTransition_source.
  unfold Elements.convert_transition in H1.
  PropUtils.destruct_match H1 ; [ PropUtils.inj H1 | discriminate H1]. (* monadInv *)
  unfold Mealy.Transition_source.
  apply OptionListUtils.find_none.
  intro e.
  intro.

  destruct e.
  {
    right.
    destruct (Elements.state_element_bw _ _ H1).
    destruct H2.
    subst.
    
    eapply OptionListUtils.find_none in H0 ; eauto.  
    destruct H0 ; [ discriminate | ].
    destruct H0 as (?&?&?).
    unfold Mealy.get_E_data.
    eexists ; split ; [ reflexivity | ].
    unfold Elements.convert. simpl.
    unfold Moore.get_E_data in H0.
    PropUtils.inj H0.
    assumption.
  }
  { left. reflexivity. }
Qed.

Lemma getTransition_source_commut_bw m t :
  Moore.WF_source m ->
  forall s t',
      Mealy.getTransition_source (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some (Elements.convert s) ->
      Elements.convert_transition m t = Some t' ->
      exists s', s'.(Moore.State_id) = s.(Moore.State_id) /\ 
      Moore.getTransition_source m t = Some s'. (* weak result because convert is not injective *)
Proof.
  intro WF ; intros.
  destruct (Mealy.getTransition_source_inv _ _ _ H).
  destruct (Elements.state_element_bw _ _ H1) as (?&?&?).
  unfold Elements.convert in H4.
  PropUtils.inj H4.

  unfold Moore.getTransition_source.
  rewrite OptionListUtils.find_lift_filter_lift.
    unfold Elements.convert_transition in H0.
  PropUtils.destruct_match H0 ; [ PropUtils.inj H0 | discriminate H0]. (* monadIv *)
  simpl in H2.
  
  cut (exists s' : Moore.State_t,
    List.find
      (fun s0 : Moore.getTypeByEKind Moore.State_K =>
       Id.NodeId_beq (Moore.Transition_source t) (Moore.State_id s0))
      (OptionListUtils.lift_list (Moore.get_E_data Moore.State_K)
         (Model.modelElements m)) = Some s').
  { 
    intros (s2&?). exists s2.
    destruct (List.find_some _ _ H0).
    split ; auto.
    apply Id.internal_NodeId_dec_bl in H6.
    rewrite <- H2.
    rewrite <- H6.
    reflexivity.
  }
  {
    eapply ListUtils.find_some_left.
    apply MooreWF.In_state. (*fixme : pas défini au bon endroit. *)
    eassumption.
    apply Id.internal_NodeId_dec_lb.
    congruence.
  }
Qed.

(* FIXME : this should be the main bw lemma *)
Corollary getTransition_source_commut_bw_alt m t :
  Moore.WF_source m ->
  forall s' t',
      Mealy.getTransition_source (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some s' ->
      Elements.convert_transition m t = Some t' ->
      exists s, s' = Elements.convert s /\ 
      Moore.getTransition_source m t = Some s. (* weak result because convert is not injective *)
Proof.
  intros.
  replace s' with (Elements.convert (Moore.Build_State_t s'.(Mealy.State_id) ""%string)) in H0.
  { 
    eapply getTransition_source_commut_bw in H0 ; eauto.
    destruct H0 as (?&?&?).
    eexists ; split ; eauto.
    unfold Elements.convert.
    destruct x ; destruct s' ; simpl in * ; congruence.
  }
  { destruct s' ; reflexivity. }
Qed.

Corollary getTransition_source_commut_none_bw m t :
  Moore.WF_source m ->
  forall t',
      Mealy.getTransition_source (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = None ->
      Elements.convert_transition m t = Some t' ->
      Moore.getTransition_source m t = None. 
Proof.
  intros.
  destruct (Moore.getTransition_source m t) eqn:? ; [ exfalso | reflexivity].
  eapply getTransition_source_commut_fw in Heqo ; eauto.
  congruence.
Qed.
 
Corollary getTransition_source_commut_none_fw_alt m t :
  Moore.WF_source m ->
  forall  t',
      Moore.getTransition_source m t = None ->
      Elements.convert_transition m t = Some t' ->
      Mealy.getTransition_source (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = None.
Proof.
  intros.
  destruct (Mealy.getTransition_source
    (Semantics.execute Moore2Mealy.Moore2Mealy m) t') eqn:?; [ exfalso | reflexivity ].
  replace s with (Elements.convert (Moore.Build_State_t s.(Mealy.State_id) " "%string)) in Heqo.

  eapply getTransition_source_commut_bw in Heqo ; eauto.
  destruct Heqo as (?&?&?).
  congruence.
  destruct s ; reflexivity.
Qed.

(** [getTransition_target] : copy/paste [getTransition_source] *)


Lemma getTransition_target_commut_fw m t :
  Moore.WF_target m ->
  forall s,
      Moore.getTransition_target m t = Some s ->
      let t' := {|
        Mealy.Transition_source := Moore.Transition_source t;
        Mealy.Transition_input := Moore.Transition_input t;
        Mealy.Transition_output := Moore.State_output s;
        Mealy.Transition_dest := Moore.Transition_dest t
      |} in 
      Elements.convert_transition m t = Some t' /\ 
      Mealy.getTransition_target (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some (Elements.convert s).
Proof.
  intros.
  unfold Elements.convert_transition.
  rewrite H0.
  split ; [ subst t' ; reflexivity | ].
  destruct (Moore.getTransition_target_inv _ _ _ H0).

  apply MealyWF.getTransition_target_some.
  { apply MealyWF.always_unique_ids. }
  { apply Elements.state_element_fw. assumption. }
  { unfold Elements.convert ; simpl. auto. }
Qed.

Lemma getTransition_target_commut_none_fw m t :
  Moore.WF_target m ->
  forall  t',
      Moore.getTransition_target m t = None ->
      Elements.convert_transition m t = Some t' ->
      Mealy.getTransition_target (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = None.
Proof.
  intros.
  unfold Moore.getTransition_target in H0.
  unfold Mealy.getTransition_target.
  unfold Elements.convert_transition in H1.
  PropUtils.destruct_match H1 ; [ PropUtils.inj H1 | discriminate H1]. (* monadInv *)
  unfold Mealy.Transition_dest.
  apply OptionListUtils.find_none.
  intro e.
  intro.

  destruct e.
  {
    right.
    destruct (Elements.state_element_bw _ _ H1).
    destruct H2.
    subst.
    
    eapply OptionListUtils.find_none in H0 ; eauto.  
    destruct H0 ; [ discriminate | ].
    destruct H0 as (?&?&?).
    unfold Mealy.get_E_data.
    eexists ; split ; [ reflexivity | ].
    unfold Elements.convert. simpl.
    unfold Moore.get_E_data in H0.
    PropUtils.inj H0.
    assumption.
  }
  { left. reflexivity. }
Qed.

Lemma getTransition_target_commut_bw m t :
  Moore.WF_target m ->
  forall s t',
      Mealy.getTransition_target (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some (Elements.convert s) ->
      Elements.convert_transition m t = Some t' ->
      exists s', s'.(Moore.State_id) = s.(Moore.State_id) /\ 
      Moore.getTransition_target m t = Some s'. (* weak result because convert is not injective *)
Proof.
  intro WF ; intros.
  destruct (Mealy.getTransition_target_inv _ _ _ H).
  destruct (Elements.state_element_bw _ _ H1) as (?&?&?).
  unfold Elements.convert in H4.
  PropUtils.inj H4.

  unfold Moore.getTransition_target.
  rewrite OptionListUtils.find_lift_filter_lift.
    unfold Elements.convert_transition in H0.
  PropUtils.destruct_match H0 ; [ PropUtils.inj H0 | discriminate H0]. (* monadIv *)
  simpl in H2.
  
  cut (exists s' : Moore.State_t,
    List.find
      (fun s0 : Moore.getTypeByEKind Moore.State_K =>
       Id.NodeId_beq (Moore.Transition_dest t) (Moore.State_id s0))
      (OptionListUtils.lift_list (Moore.get_E_data Moore.State_K)
         (Model.modelElements m)) = Some s').
  { 
    intros (s2&?). exists s2.
    destruct (List.find_some _ _ H0).
    split ; auto.
    apply Id.internal_NodeId_dec_bl in H6.
    rewrite <- H2.
    rewrite <- H6.
    reflexivity.
  }
  {
    eapply ListUtils.find_some_left.
    apply MooreWF.In_state. (*fixme : pas défini au bon endroit. *)
    eassumption.
    apply Id.internal_NodeId_dec_lb.
    congruence.
  }
Qed.

(* FIXME : this should be the main bw lemma *)
Corollary getTransition_target_commut_bw_alt m t :
  Moore.WF_target m ->
  forall s' t',
      Mealy.getTransition_target (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some s' ->
      Elements.convert_transition m t = Some t' ->
      exists s, s' = Elements.convert s /\ 
      Moore.getTransition_target m t = Some s. (* weak result because convert is not injective *)
Proof.
  intros.
  replace s' with (Elements.convert (Moore.Build_State_t s'.(Mealy.State_id) ""%string)) in H0.
  { 
    eapply getTransition_target_commut_bw in H0 ; eauto.
    destruct H0 as (?&?&?).
    eexists ; split ; eauto.
    unfold Elements.convert.
    destruct x ; destruct s' ; simpl in * ; congruence.
  }
  { destruct s' ; reflexivity. }
Qed.

Lemma getTransition_target_commut_bw_alt_alt m :
  Moore.WF_target m ->
  forall s' t',
    List.In (Mealy.TransitionElement t') (Semantics.execute Moore2Mealy.Moore2Mealy m).(Model.modelElements) ->  
      Mealy.getTransition_target (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some s' ->
      exists t,
      Elements.convert_transition m t = Some t' /\
      exists s, s' = Elements.convert s /\ 
      Moore.getTransition_target m t = Some s. (* weak result because convert is not injective *)
Proof.
  intros WF ; intros s' t' T_IN1 T_G. 
  destruct (Mealy.getTransition_target_inv _ _ _ T_G) as (T_IN2 & T_E).

  apply Elements.transition_element_bw in T_IN1 ; eauto.
  destruct T_IN1 as (t & IN1 & T).
  exists t.
  split ; [ congruence | ].
  eapply getTransition_target_commut_bw_alt ; eauto.
Qed.

Corollary getTransition_target_commut_none_bw m t :
  Moore.WF_target m ->
  forall t',
      Mealy.getTransition_target (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = None ->
      Elements.convert_transition m t = Some t' ->
      Moore.getTransition_target m t = None. 
Proof.
  intros.
  destruct (Moore.getTransition_target m t) eqn:? ; [ exfalso | reflexivity].
  apply getTransition_target_commut_fw in Heqo ; eauto.
  destruct Heqo.
  congruence.
Qed.
 
Corollary getTransition_target_commut_none_fw_alt m t :
  Moore.WF_target m ->
  forall  t',
      Moore.getTransition_target m t = None ->
      Elements.convert_transition m t = Some t' ->
      Mealy.getTransition_target (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = None.
Proof.
  intros.
  destruct (Mealy.getTransition_target
    (Semantics.execute Moore2Mealy.Moore2Mealy m) t') eqn:?; [ exfalso | reflexivity ].
  replace s with (Elements.convert (Moore.Build_State_t s.(Mealy.State_id) " "%string)) in Heqo.

  eapply getTransition_target_commut_bw in Heqo ; eauto.
  destruct Heqo as (?&?&?).
  congruence.
  destruct s ; reflexivity.
Qed.
