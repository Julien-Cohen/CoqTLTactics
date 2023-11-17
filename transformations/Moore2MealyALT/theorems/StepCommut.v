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

Section Foo.

Variable (m:Moore.M).

Hypothesis WF_S : Moore.WF_source m.
Hypothesis WF_T : Moore.WF_target m.
Hypothesis WF_D : MooreWF.determinist m.

(** [State_outTransitions] *)


Lemma in_outTransitions_commut_fw t s t' :
  List.In t (MooreSemantics.State_outTransitions m s) ->
  Elements.convert_transition m t = Some t' ->
  List.In t' (MealySemantics.State_outTransitions
                (Semantics.execute Moore2Mealy.Moore2Mealy m)
                (Elements.convert_state s)).
Proof.
  intros.
  destruct (MooreSemantics.State_out_transitions_inv  _ _ _ H).
  apply Elements.transition_element_fw in H1 ; auto.
  destruct H1 as (?&?&?).
  PropUtils.unif H0 H1. (* pourquoi ? *)

  destruct (Elements.convert_transition_nec _ _ _ H0) as (?&?&?).
  subst.
  
  apply MealySemantics.in_State_outTransitions.
  { assumption.    }        
  { eapply GettersCommut.getTransition_source_commut_fw ; eauto. }
Qed.


Lemma in_outTransitions_commut_bw t s' t' :
  List.In t' 
    (MealySemantics.State_outTransitions (Semantics.execute Moore2Mealy.Moore2Mealy m) s') ->
  Elements.convert_transition m t = Some t' ->
  exists s, Elements.convert_state s = s'
            /\ List.In t (MooreSemantics.State_outTransitions m s).
Proof.
  intros.
  destruct (MealySemantics.State_out_transitions_inv  _ _ _ H).
  apply Elements.transition_element_bw in H1 ; auto.
  destruct H1 as (?&?&?).

  replace x with t in *.
  2:{ eapply Elements.convert_transition_injective ; eauto. }
   
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

Lemma in_outTransitions_commut_bw_2 s' t' :
  List.In t' 
    (MealySemantics.State_outTransitions (Semantics.execute Moore2Mealy.Moore2Mealy m) s') ->
  exists t,  
    Elements.convert_transition m t = Some t'
    /\ exists s,
      Elements.convert_state s = s' 
      /\ List.In t (MooreSemantics.State_outTransitions m s).
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
    destruct (MealySemantics.State_out_transitions_inv  _ _ _ H).
    unfold Elements.convert_transition.
    cut (Mealy.WF_target (Semantics.execute Moore2Mealy.Moore2Mealy m)) ; auto with wf.
    intro WF.
    destruct  (WF _ H0).
    eapply GettersCommut.getTransition_target_commut_bw in H2 ; eauto.
    destruct H2 as (t & ?& ?& ? & ?).
    exists t.
    rewrite H4.
    subst.
    f_equal.
    unfold Elements.convert_transition in H2.
    rewrite H4 in H2.
    PropUtils.inj H2.
    reflexivity.
  }
Qed.


(** [State_acceptTransition] *)

Lemma State_acceptTransition_commut_fw :
  forall s i t,
    MooreSemantics.State_acceptTransition m s i = Some t ->
    MealySemantics.State_acceptTransition (Semantics.execute Moore2Mealy.Moore2Mealy m) (Elements.convert_state s) i = Elements.convert_transition m t.
Proof.
  intros s i t A.

  destruct (MooreSemantics.State_acceptTransition_inv _ _ _ _ A).
  
  destruct (MooreSemantics.State_out_transitions_inv  _ _ _ H). 
  unfold Elements.convert_transition.
  destruct (WF_T _ H1) as (s' & H4).
  rewrite H4.
  apply MealyWF.State_acceptTransition_some ; auto with wf.

  eapply in_outTransitions_commut_fw ; eauto.

  unfold Elements.convert_transition. rewrite H4. reflexivity.

Qed.

Lemma State_acceptTransition_commut_bw :
  forall s' i t',
    MealySemantics.State_acceptTransition (Semantics.execute Moore2Mealy.Moore2Mealy m) s' i = Some t' ->
    
    exists s, 
      Elements.convert_state s = s' 
      /\ exists t,
        Elements.convert_transition m t = Some t' 
        /\ MooreSemantics.State_acceptTransition m s i = Some t.
Proof.
  intros.

  destruct (MealySemantics.State_acceptTransition_inv _ _ _ _ H).

  eapply in_outTransitions_commut_bw_2 in H0 ; eauto.
  destruct H0 as (t&?& s & ? & ?).
  exists s ; split ; auto.
  exists t ; split ; auto.
  unfold MooreSemantics.State_acceptTransition.
  apply ListUtils.in_find ; eauto.
  { apply MooreWF.truc. assumption. }
  { apply String.eqb_eq.
    destruct (Elements.convert_transition_nec _ _ _ H0) as (?& _ &?).
    subst.
    reflexivity.
  }
Qed.

(** [ search] *)

Lemma search_commut_fw :
  forall s1 i s2,
    MooreSemantics.search m s1 i = Some s2 ->
    exists s1' s2',
      s1'= Elements.convert_state s1 
      /\ s2'= Elements.convert_state s2 
      /\ exists t',
        MealySemantics.search (Semantics.execute Moore2Mealy.Moore2Mealy m) s1' i = Some (t',s2') 
        /\ Mealy.Transition_output t' = Moore.State_output s2.
Proof.    
  intros.
  
  destruct (MooreSemantics.search_inv _ _ _ _ H) as (?&?&?).

  unfold MealySemantics.search.
  unfold Elements.convert_state.
  eexists ; eexists ; split ; eauto. split ; eauto.
  apply State_acceptTransition_commut_fw in H0 ; auto.
  unfold Elements.convert_state in H0.
  rewrite H0.
  destruct (GettersCommut.getTransition_target_commut_fw _ _ _ H1).

  rewrite H2.

  rewrite H3.
  unfold Elements.convert_state.
  eauto.
Qed.

Lemma search_commut_bw :
  forall s1' i s2' t',
 MealySemantics.search (Semantics.execute Moore2Mealy.Moore2Mealy m) s1' i = Some (t',s2') ->
    exists s1,
      s1'= Elements.convert_state s1 
      /\ exists s2, 
        s2'= Elements.convert_state s2 
        /\ MooreSemantics.search m s1 i = Some s2 
        /\ Mealy.Transition_output t' = Moore.State_output s2.        
Proof.    
  intros.
  
  destruct (MealySemantics.search_inv _ _ _ _ _ H).

  unfold MooreSemantics.search.
  
  destruct (State_acceptTransition_commut_bw  _ _ _ H0) as (s1 & ? & t & ? & ?).

  exists s1. split ; auto.
  rewrite H4.

  destruct (MealySemantics.State_acceptTransition_inv _ _ _ _ H0).
  
  destruct (MealySemantics.State_out_transitions_inv _ _ _ H5).

  destruct (GettersCommut.getTransition_target_commut_bw _ WF_T _ _ H7 H1) as (?&?&s2&?&?).
  replace x with t in *.
  2:{ eapply Elements.convert_transition_injective ; eauto. }
  clear H8. (* duplicate *)
  rewrite H10.
  destruct (Elements.convert_transition_nec _ _ _ H3) as (?&?&?) ; subst t'.
  simpl.
  PropUtils.unif H11 H8.
  eauto.
Qed.


End Foo.
