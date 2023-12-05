Require Moore2Mealy.MooreSemantics.
Require Moore2Mealy.MealySemantics.
Require Moore2Mealy.Moore2Mealy.
Require Moore2Mealy.MooreWF.
Require Moore2Mealy.MealyWF.
Require Moore2Mealy.theorems.Elements.
Require Moore2Mealy.theorems.WFStable.

Import String.

Section Foo.

Variable (m:Moore.M).

Hypothesis WF_S : Moore.WF_transition_source_exists m.
Hypothesis WF_T : Moore.WF_transition_target_exists m.
Hypothesis WF_1 : MooreWF.WF_transition_source_uniqueness m.
Hypothesis WF_2 : Moore.WF_transition_source_glue_l_exists m.
Hypothesis WF_3 : Moore.WF_transition_source_glue_r_exists m.
Hypothesis WF_4 : MooreWF.WF_transition_target_uniqueness m.
Hypothesis WF_5 : Moore.WF_transition_target_glue_l_exists m.
Hypothesis WF_6 : Moore.WF_transition_target_glue_r_exists m.
Hypothesis WF_7 : MooreWF.state_id_uniqueness m.

Lemma getTransition_source_commut_fw t :
  forall s t',
      Moore.getTransition_source m t = Some s ->
      Moore2Mealy.convert_transition m t = Some t' ->
      Mealy.getTransition_source (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some (Moore2Mealy.convert_state s).
Proof.
  intros.
  apply Moore.getTransition_source_inv in H.

  apply MealyWF.getTransition_source_some.
  {  auto with wf.  }
  { apply Elements.state_element_fw. apply WF_3 in H. (* FIXME : pas pratique).*) exact H. }
  { 
    apply Links.source_link_fw in H ; auto.
    destruct H as (t'' & C & IN). (* fixme : faire un lemme intermédiaire*)
    rewrite C in H0 ; PropUtils.inj H0.
    exact IN.
  }
Qed.


Lemma getTransition_source_commut_bw t :
  forall s t',
      Mealy.getTransition_source (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some (Moore2Mealy.convert_state s) ->
      Moore2Mealy.convert_transition m t = Some t' ->
      exists s', s'.(Moore.State_id) = s.(Moore.State_id) /\ 
      Moore.getTransition_source m t = Some s'. (* weak result because convert is not injective *)
Proof.
  intros s t' G C. 

  (* on sait que la recherche de source pour une transition t' donnée a fonctionné et donne un état "convert s" *)



  specialize (Mealy.getTransition_source_inv _ _ _ G) ; intro H1.

(* on a déduit que t' est bien dans le modèle transformé m'. *)

  unfold Moore.WF_transition_source_glue_l_exists in WF_2.
  cbv zeta in H1.

(*  specialize (WF_2 _ H1).*)

(*  Soit appeler une tactique BW, soit s'appuyer sur Elements et Links. *)

(* Ici on veut un Link/BW *)
  apply Links.source_link_bw in H1 ; [ | exact WF_S].

(* Si convert_state est injective, alors le s0 qui existe est égal à s. *)

  destruct H1 as (s'&E&IN).
  exists s'.
  split.
  + destruct s ; destruct s' ; PropUtils.inj E. reflexivity.
  +
    
    unfold Moore.getTransition_source.
    unfold Moore.getTransition_sourceOnLinks.
    
    match type of IN with List.In (Moore.TransitionSource ?g) _ =>
                            remember g as g0
    end.
    apply OptionUtils.option_map_some with (b:=g0) ; [ | subst ; reflexivity ].

    apply OptionListUtils.in_find_lift with (e:=Moore.TransitionSource g0) ; [ | reflexivity | subst ; simpl  |  exact IN]
    .
    shelve.
    destruct t.
    
    unfold Moore2Mealy.convert_transition in C.
    OptionUtils.monadInv C.
    simpl in *.
    rewrite Moore.internal_nat_dec_lb ; try reflexivity.
    rewrite Id.internal_string_dec_lb ; try reflexivity.

    Unshelve.
    unfold ListUtils.discriminating_predicate.
    intros a b IN1 IN2 E1 E2.

    apply Moore.internal_Transition_t_dec_bl in E1.
    apply Moore.internal_Transition_t_dec_bl in E2.
    apply OptionListUtils.In_lift in IN1.
    apply OptionListUtils.In_lift in IN2.

    destruct IN1 as (l1&G1&IN1).
    destruct IN2 as (l2&G2&IN2).


    unfold Moore.get_L_data in G1, G2 ; simpl in *.

    destruct l1 ; [ PropUtils.inj G1 |  discriminate ]. 
    destruct l2 ; [ PropUtils.inj G2 |  discriminate ]. 

    apply WF_1 ; auto.

Qed.

(* FIXME : this should be the main bw lemma *)
Corollary getTransition_source_commut_bw_alt t :
  forall s' t',
      Mealy.getTransition_source (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some s' ->
      Moore2Mealy.convert_transition m t = Some t' ->
      exists s, s' = Moore2Mealy.convert_state s /\ 
                  Moore.getTransition_source m t = Some s. (* weak result because convert is not injective *)
Proof.
  intros.
  replace s' with (Moore2Mealy.convert_state (Moore.Build_State_t s'.(Mealy.State_id) ""%string)) in H.
  { 
    eapply getTransition_source_commut_bw in H ; eauto.
    destruct H as (?&?&?).
    eexists ; split ; eauto.
    unfold Moore2Mealy.convert_state.
    destruct x ; destruct s' ; simpl in * ; congruence.
  }
  { destruct s' ; reflexivity. }
Qed.


(** [getTransition_target] *)

Lemma getTransition_target_commut_fw t :
  forall s,
      Moore.getTransition_target m t = Some s ->
      let t' := {|
        Mealy.Transition_id := Moore.Transition_id t ;
        Mealy.Transition_input := Moore.Transition_input t;
        Mealy.Transition_output := Moore.State_output s;
      |} in 
      Moore2Mealy.convert_transition m t = Some t' /\ 
      Mealy.getTransition_target (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some (Moore2Mealy.convert_state s).
Proof.
  intros.
  unfold Moore2Mealy.convert_transition.
  rewrite H.
  split ; [ subst t' ; reflexivity | ].
  PropUtils.duplicate H H'.
  apply Moore.getTransition_target_inv in H.

  apply MealyWF.getTransition_target_some.

  { auto with wf. }
  { apply Elements.state_element_fw. 
    apply WF_6 in H. assumption. }
  { 
    apply Links.target_link_fw in H ; auto ; [].
    destruct H as (?&?&?).
    replace t' with x ; [ assumption | ].
    unfold Moore2Mealy.convert_transition in H.
    rewrite H' in H.
    PropUtils.inj H.
        subst t'.
    reflexivity.
  }


Qed.


Lemma getTransition_target_commut_bw :
  forall s' t',
    List.In (Mealy.Transition t') (Semantics.execute Moore2Mealy.Moore2Mealy m).(Model.modelElements) ->  
      Mealy.getTransition_target (Semantics.execute Moore2Mealy.Moore2Mealy m) t' = Some s' ->
      exists t,
      Moore2Mealy.convert_transition m t = Some t' /\
      exists s, s' = Moore2Mealy.convert_state s /\ 
      Moore.getTransition_target m t = Some s. 
Proof.
  intros s t' IN_E_MEALY G_MEALY.
  PropUtils.duplicate G_MEALY IN_L_MEALY.
  apply Mealy.getTransition_target_inv in IN_L_MEALY.
  PropUtils.duplicate IN_E_MEALY IN_E_MOORE.
  apply Elements.transition_element_bw in IN_E_MOORE.
  destruct IN_E_MOORE as (t0 & IN_E_MOORE & C).
  rewrite C.
  exists t0 ; split ; [reflexivity | ].

  cut (List.In (Mealy.State s) (Model.modelElements
                                  (Semantics.execute Moore2Mealy.Moore2Mealy m))).

  {
    intro IN_STATE_MEALY.
    apply Elements.state_element_bw in IN_STATE_MEALY.
    destruct IN_STATE_MEALY as (s0 & IN_STATE_MOORE & C_S).
    exists s0.
    split ; [ auto | ].
    apply MooreWF.getTransition_target_some ; auto ; [].
    apply Links.target_link_bw in IN_L_MEALY.
    destruct IN_L_MEALY as (s1 & C_S_1 & IN_TT_MOORE).
    cut (s0 = s1).
    { 
      intro ; subst s0. clear C_S.
      unfold Moore2Mealy.convert_transition in C.
      PropUtils.destruct_match_H C ; [       PropUtils.inj C | discriminate C ].
      simpl in IN_TT_MOORE.
      destruct t0 ; exact IN_TT_MOORE.
    }
    { 
      eapply Elements.convert_state_injective ; eauto with wf.  
      apply WF_6 in IN_TT_MOORE ; exact IN_TT_MOORE.
      congruence.
    }
  }
  { 
    apply WFStable.transition_target_glue_r_exists_stable in WF_6. 
    apply WF_6 in IN_L_MEALY. 
    exact IN_L_MEALY.
  }
Qed.


End Foo.
