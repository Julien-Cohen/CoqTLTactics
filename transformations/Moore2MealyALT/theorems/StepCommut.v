Require Moore2MealyALT.MooreSemantics.
Require Moore2MealyALT.MealySemantics.
Require Moore2MealyALT.Moore2Mealy.
Require Moore2MealyALT.MooreWF.
Require Moore2MealyALT.MealyWF.
Require Moore2MealyALT.theorems.Elements.
Require Moore2MealyALT.theorems.WFStable.
Require Moore2MealyALT.theorems.InitStable.
Require Moore2MealyALT.theorems.GettersCommut.

Import String OptionUtils.


(** [State_outTransitions] *)


Lemma in_outTransitions_commut_fw m t s t' :
  Moore.WF_source m ->
  Moore.WF_target m ->
  MooreWF.determinist m ->

    List.In t (MooreSemantics.State_outTransitions m s) ->
    Elements.convert_transition m t = Some t' ->
    List.In t' (MealySemantics.State_outTransitions
       (Semantics.execute Moore2Mealy.Moore2Mealy m)
       (Elements.convert s)).
Proof.
  intros WF1 WF2 WF3. intros.
  destruct (MooreSemantics.State_out_transitions_inv  _ _ _ H).
  apply Elements.transition_element_fw in H1 ; auto.
  destruct H1 as (?&?&?).
  rewrite H0 in H1. PropUtils.inj H1. (* unif *) (* pourquoi ? *)

  destruct (Elements.convert_transition_inv _ _ _ H0) as (?&?&?).
  subst.
  
  apply MealySemantics.in_State_outTransitions.
  { assumption.    }        
  { eapply GettersCommut.getTransition_source_commut_fw ; eauto. }
Qed.


Lemma in_outTransitions_commut_bw m t s' t' :
  Moore.WF_source m ->
  Moore.WF_target m ->
  MooreWF.determinist m ->

    List.In t' 
      (MealySemantics.State_outTransitions (Semantics.execute Moore2Mealy.Moore2Mealy m) s') ->
    Elements.convert_transition m t = Some t' ->
    exists s, Elements.convert s = s' /\
    List.In t (MooreSemantics.State_outTransitions m s).
Proof.
  intros WF1 WF2 WF3. intros.
  destruct (MealySemantics.State_out_transitions_inv  _ _ _ H).
  apply Elements.transition_element_bw in H1 ; auto.
  destruct H1 as (?&?&?).

  


  replace x with t in *.
  2:{ eapply Elements.convert_transition_inj ; eauto. }
  
  
  clear H3.
  eapply GettersCommut.getTransition_source_commut_bw_alt in H2 ; eauto.

    unfold MooreSemantics.State_outTransitions.
    destruct H2 as (s & ? & ?).
    exists s.
    split ; auto.
    

    apply OptionListUtils.filter_lift_in.
    rewrite H3.
    eexists ; split ; eauto.
    split ; eauto.
    apply Moore.internal_State_t_dec_lb.
    reflexivity.
Qed.

Lemma in_outTransitions_commut_bw_2 m s' t' :
  Moore.WF_source m ->
  Moore.WF_target m ->
  MooreWF.determinist m ->

    List.In t' 
      (MealySemantics.State_outTransitions (Semantics.execute Moore2Mealy.Moore2Mealy m) s') ->
    exists t,  Elements.convert_transition m t = Some t' /\
    exists s, Elements.convert s = s' /\
                 
    List.In t (MooreSemantics.State_outTransitions m s).
Proof.
  intros.
  cut (exists t : Moore.Transition_t,
          Elements.convert_transition m t = Some t').
  { 
    intros (t & ?).
    exists t ; split ; auto.
    eapply in_outTransitions_commut_bw ; eauto.
  }    
  {
    destruct (MealySemantics.State_out_transitions_inv  _ _ _ H2).
    unfold Elements.convert_transition.
    cut (Mealy.WF_target (Semantics.execute Moore2Mealy.Moore2Mealy m)) ; auto with wf.
    intro WF.
    destruct  (WF _ H3).
    eapply GettersCommut.getTransition_target_commut_bw_alt_alt in H5 ; eauto.
    destruct H5 as (t & ?& ?& ? & ?).
    exists t.
    rewrite H7.
    subst.
    f_equal.
    unfold Elements.convert_transition in H5.
    rewrite H7 in H5.
    PropUtils.inj H5.
    reflexivity.
  }
Qed.

(** [State_acceptTransition] *)

Lemma State_acceptTransition_commut_fw :
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
  

  apply String.eqb_eq in H2. subst.
  
  destruct (MooreSemantics.State_out_transitions_inv  _ _ _ H1). 
  unfold Elements.convert_transition.
  destruct (WF_2  _ H) as (s' & H4).
  rewrite H4.
  apply MealyWF.State_acceptTransition_some ; auto with wf.

  eapply in_outTransitions_commut_fw ; eauto.

  unfold Elements.convert_transition. rewrite H4. reflexivity.

Qed.

Lemma State_acceptTransition_commut_bw :
  forall s' m i t',
    Moore.WF_source m ->
    Moore.WF_target m ->
    MooreWF.determinist m ->
    MealySemantics.State_acceptTransition (Semantics.execute Moore2Mealy.Moore2Mealy m) s' i = Some t' ->

    exists s, Elements.convert s = s' /\ 
                exists t,
                  Elements.convert_transition m t = Some t' /\
                    MooreSemantics.State_acceptTransition m s i = Some t 
    .
Proof.
  intros.
  unfold MealySemantics.State_acceptTransition in H2.
  destruct (List.find_some _ _ H2).
  eapply in_outTransitions_commut_bw_2 in H3 ; eauto.
  destruct H3 as (t&?& s & ? & ?).
  exists s ; split ; auto.
  exists t ; split ; auto.
  unfold MooreSemantics.State_acceptTransition.
  apply ListUtils.in_find ; eauto.
  { apply MooreWF.truc. assumption. }
  { apply String.eqb_eq. apply String.eqb_eq in H4.
    destruct (Elements.convert_transition_inv _ _ _ H3) as (?& _ &?).
    subst.
    reflexivity.
  }
Qed.

Corollary State_acceptTransition_none_commut_fw :
  forall s m i,
    MooreWF.unique_ids m ->
    Moore.WF_source m ->
    Moore.WF_target m ->
    MooreWF.determinist m ->
    List.In (Moore.StateElement s) (Model.modelElements m) ->
    MooreSemantics.State_acceptTransition m s i = None ->
    MealySemantics.State_acceptTransition (Semantics.execute Moore2Mealy.Moore2Mealy m) (Elements.convert s) i = None.
Proof.
  intros s m i WF_0 WF_1 WF_2 WF_3 IN A.

  destruct (MealySemantics.State_acceptTransition
    (Semantics.execute Moore2Mealy.Moore2Mealy m)
    (Elements.convert s) i) eqn:? ; [ exfalso | reflexivity ].
  apply State_acceptTransition_commut_bw in Heqo ; auto.
  destruct Heqo as (x & ? & ? & _ & ?).
  replace x with s in H0.
  congruence.
  apply WF_0 ; auto.
  + (* inv *) unfold MooreSemantics.State_acceptTransition in H0.
    destruct (List.find_some _ _ H0).
    destruct (MooreSemantics.State_out_transitions_inv _ _ _ H1).
    destruct (Moore.getTransition_source_inv _ _ _ H4).
    assumption.
  + destruct x ; destruct s ; unfold Elements.convert in H ; simpl in H. simpl. congruence.
Qed.   

(** [ search] *)


Lemma search_commut_fw m :
  Moore.WF_source m ->
  Moore.WF_target m ->
  MooreWF.determinist m ->
  forall s1 i s2,
    MooreSemantics.search m s1 i = Some s2 ->
    exists s1' s2',
      s1'= Elements.convert s1 /\
        s2'= Elements.convert s2 /\ 
        exists t',
          MealySemantics.search (Semantics.execute Moore2Mealy.Moore2Mealy m) s1' i = Some (t',s2').
Proof.    
  intros WF1 WF2 WF3.
  intros.
  
  (* inversion H *)
  unfold MooreSemantics.search in H.
  PropUtils.destruct_match H ; [ | discriminate H].
  

  unfold MealySemantics.search.
  unfold Elements.convert.
  eexists ; eexists ; split ; eauto. split ; eauto.
  apply State_acceptTransition_commut_fw in Heqo ; auto.
  unfold Elements.convert in Heqo.
  rewrite Heqo.
  destruct (GettersCommut.getTransition_target_commut_fw _ _ WF2 _ H).

  rewrite H0.

  rewrite H1.
  unfold Elements.convert.
  eauto.
Qed.

Lemma search_commut_bw m :
  Moore.WF_source m ->
  Moore.WF_target m ->
  MooreWF.determinist m ->
  forall s1' i s2' t',
 MealySemantics.search (Semantics.execute Moore2Mealy.Moore2Mealy m) s1' i = Some (t',s2') ->
    exists s1,
      s1'= Elements.convert s1 /\
        exists s2, 
          s2'= Elements.convert s2 /\ 
            MooreSemantics.search m s1 i = Some s2
          .
Proof.    
  intros WF1 WF2 WF3 ; intros.
  
  (* inversion *)
  unfold MealySemantics.search in H.
  PropUtils.destruct_match H ; [ | discriminate  H].
  PropUtils.destruct_match H ; [ PropUtils.inj H | discriminate H].


  unfold MooreSemantics.search.
  
  destruct (State_acceptTransition_commut_bw _ _ _ _ WF1 WF2 WF3 Heqo) as (s1 & ? & t & ? & ?).

  exists s1. split ; auto.
  rewrite H1.

  (* inversion *)
  unfold MealySemantics.State_acceptTransition in Heqo.
  apply List.find_some in Heqo.
  destruct Heqo.

  apply MealySemantics.State_out_transitions_inv in H2.
  destruct H2.
  destruct (GettersCommut.getTransition_target_commut_bw_alt_alt _ WF2 _ _ H2 Heqo0) as (?&?&s2&?&?).
  replace x with t in *.
  2:{
    eapply Elements.convert_transition_inj ; eauto.
  }
  clear H5.
  rewrite H7.
  eauto.
Qed.
