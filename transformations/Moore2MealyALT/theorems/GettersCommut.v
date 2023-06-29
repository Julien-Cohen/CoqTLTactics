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

  destruct (Elements.convert_transition_inv _ _  _ H0) as  (s0 & Heqo & E) ; subst t'.

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


(** [getTransition_target] *)

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


Lemma getTransition_target_commut_bw m :
  Moore.WF_target m ->
  forall s' t',
    List.In (Mealy.TransitionElement t') (Semantics.execute Moore2Mealy.Moore2Mealy m).(Model.modelElements) ->  
      Mealy.getTransition_target (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some s' ->
      exists t,
      Elements.convert_transition m t = Some t' /\
      exists s, s' = Elements.convert s /\ 
      Moore.getTransition_target m t = Some s. 
Proof.
  intro WF ; intros.
  destruct (Mealy.getTransition_target_inv _ _ _ H0).
  destruct (Elements.state_element_bw _ _ H1) as (s&?&?).
  destruct (Elements.transition_element_bw _ _ WF H) as (t&?&?).

  exists t.
  split ; auto.
  apply eq_sym in H6.
  destruct (Elements.convert_transition_inv _ _ _ H6) as (s2&?&?) ; subst t'.
  exists s2.
  split ; auto.
  simpl in H2.
  destruct s', s2.
  unfold Elements.convert.
  f_equal. simpl.
  destruct (Moore.getTransition_target_inv _ _ _ H7). simpl in H9.
  clear H7.
  simpl in H2.
  congruence.
Qed.

