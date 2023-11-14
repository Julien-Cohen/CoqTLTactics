Require Moore2Mealy.MooreSemantics.
Require Moore2Mealy.MealySemantics.
Require Moore2Mealy.Moore2Mealy.
Require Moore2Mealy.MooreWF.
Require Moore2Mealy.MealyWF.

Require Moore2Mealy.theorems.Elements.
Require Moore2Mealy.theorems.TraceUtils.

Import OptionUtils List.
Import String. (* for notation *)
Import Model.

Import Glue.

Import Moore2Mealy.

Section Foo.

Variable (m:Moore.M).

Hypothesis WF_U : MooreWF.state_id_uniqueness m.
Hypothesis WF_T : Moore.WF_transition_target_exists m.
Hypothesis WF_S : Moore.WF_transition_source_exists m.
Hypothesis WF_S_L : Moore.WF_transition_source_glue_l_exists m.
Hypothesis WF_S_R : Moore.WF_transition_source_glue_r_exists m.
Hypothesis WF_T_L : Moore.WF_transition_target_glue_l_exists m.
Hypothesis WF_T_R : Moore.WF_transition_target_glue_r_exists m.
Hypothesis WF_TLL : MooreWF.WF_transition_dest_uniqueness m.
Hypothesis WF_SLL : MooreWF.WF_transition_source_uniqueness m.

(* tactic (tentative) *)
Lemma In_1 {A} :
      forall (e:A) s,
      (exists r, s = e :: r) -> In e s.
Proof.
  intros e s (r&E) ; subst s. 
  apply in_eq.
Qed.

(* tactic (tentative) *)
Lemma In_2 {A} :
      forall (e:A) s,
      (exists a r, s = a :: e :: r) -> In e s.
Proof.
  intros e s (a&r&E) ; subst s. 
  apply in_cons. apply in_eq.
Qed.


Lemma source_link_fw :
  forall t s1,
    In (Moore.TransitionSource {| left_glue := t ; right_glue := s1 |}) m.(modelLinks) ->
    exists t', 
      Elements.convert_transition m t = Some t' /\
        In  (Mealy.TransitionSource 
               {| left_glue := t' ; right_glue := Elements.convert_state s1 |})
           (Semantics.execute Moore2Mealy m).(modelLinks).
Proof.
  intros t s1 H.

  assert (In (Moore.State s1) m.(modelElements)).
  {
    apply  WF_S_R in H. 
    assumption.
  }
  assert (In (Moore.Transition t) m.(modelElements)).
  {
    apply  WF_S_L in H. 
    assumption.
  }
  destruct (Elements.convert_transition_suff _ WF_T _ H1) as (t' & T).
  destruct (Elements.convert_transition_nec _ _ _ T) as ( s2 & G & ?).

  exists t' ; split ; [assumption | ].

  specialize (TraceUtils.state_in_trace m s1 H0) ; intro IN_TRACE.


  eapply Tactics.in_links_fw with (tc:=Moore2MealyTransformationConfiguration).
  3:{
    (* Only the second rule builds links. *)
    apply In_2. (* second rule *)
    eexists ; eexists. reflexivity.
  }
  { 
    (* The source pattern is the considered transition *)
    apply ListUtils.incl_singleton.
    exact H1.
  }
  { (* arity *)
    compute. auto. }
  { (* eval guard *) reflexivity. }
  { (* eval iterator *) compute. eauto. }
  { (* output pattern *)
    (* This rule has one output pattern. *)    
    apply In_1.
    eexists ; reflexivity.
  }
  { (* eval output pattern *)
    reflexivity.
  }



  { (* eval output pattern link *)
    (* the output patern in this rule has two link patterns. *)
    (* Transition sources are managed by the first link pattern. *)

    unfold UserExpressions.evalOutputPatternLink, 
      Parser.parseOutputPatternUnit, 
      Syntax.opu_link,
      ConcreteSyntax.r_InKinds,
      ConcreteSyntax.e_OutKind,
      ConcreteSyntax.e_outlink, 
      ConcreteSyntax.e_outpat.
    

    unfold Parser.dropToList,
      Parser.parseOutputPatternLinks, 
      Parser.parseOutputPatternLink.
    unfold  OptionListUtils.optionListToList.

    simpl ModelingMetamodel.constructor.
    rewrite G.
    simpl valueOption.

    rewrite <- H2.

    apply in_flat_map.
    eexists ; split.
    { (* first link pattern *) apply in_eq. }
    {
      unfold ConcreteSyntax.o_OutRefKind, ConcreteSyntax.o_outpat.

      unfold ConcreteExpressions.makeLink, ConcreteExpressions.wrapLink, ConcreteExpressions.wrap,  ModelingMetamodel.toEData.
      simpl.
      unfold Moore.Transition_getSourceObject .

      specialize (MooreWF.getTransition_source_some m  WF_SLL s1 H0 t H) ; intro S.
      rewrite S.
      simpl.


      eapply TraceUtils.in_Resolve_trace_2 in H0.
      unfold ModelingSemantics.resolve. 
      unfold ListUtils.singleton.
      rewrite H0.
      simpl.
      left.
      reflexivity.
    }
  }
  Unshelve. (* why ? *)
  exact 0.
Qed.


Lemma target_link_fw :
  forall t s1,
    In (Moore.TransitionTarget {| left_glue := t ; right_glue := s1 |}) m.(modelLinks) ->
    exists t', 
      Elements.convert_transition m t = Some t' /\
        In  
          (Mealy.TransitionTarget {| left_glue := t' ; right_glue := Elements.convert_state s1 |}) 
          (Semantics.execute Moore2Mealy m).(modelLinks).
Proof.
  intros t s1 H.

  assert (In (Moore.State s1) m.(modelElements)).
  {
    apply  WF_T_R in H. 
    assumption.
  }
  assert (In (Moore.Transition t) m.(modelElements)).
  {
    apply  WF_T_L in H. 
    assumption.
  }
  destruct (Elements.convert_transition_suff _ WF_T _ H1) as (t' & T).
  destruct (Elements.convert_transition_nec _ _ _ T) as ( s2 & ?& ?).

  exists t' ; split ; [assumption | ].

  specialize (TraceUtils.state_in_trace m s1 H0) ; intro INTRACE.


  eapply Tactics.in_links_fw with (tc:=Moore2MealyTransformationConfiguration).
  3:{
    (* only the second rule builds links. *)
    apply In_2. (* second rule *)
    eexists ; eexists ; reflexivity. 
  }
  { 
    (* the source pattern is the considered transition *)
    apply ListUtils.incl_singleton.
    exact H1.
  }
  { (* arity *)
    compute ; auto. }
  { (* eval guard *) reflexivity. }
  { (* eval iterator *) compute. eauto. }
  { (* output pattern *)
    (* this rule has one output pattern *)
    apply In_1. eexists ; reflexivity. 
  }
  { (* eval output pattern *)
    reflexivity.
  }


  { (* eval output pattern link *)
    (* the output patern in this rule has two link patterns. *)
    (* Transition targets are managed by the second link pattern. *)

    unfold ConcreteSyntax.e_OutKind.
    unfold ConcreteSyntax.e_outpat.
    unfold Parser.parseOutputPatternUnit.    
    unfold UserExpressions.evalOutputPatternLink.
    unfold Syntax.opu_link.
    unfold ConcreteSyntax.e_OutKind.
    unfold ConcreteSyntax.e_outlink.
    unfold Parser.dropToList.
    unfold Parser.parseOutputPatternLink.
    unfold Parser.parseOutputPatternLinks.
    apply OptionListUtils.in_optionListToList.
    eexists ; split ; [ reflexivity| ].
    apply in_flat_map.
    eexists ; split.
    { (* second link pattern *) apply In_2; eauto. }
    {
      rewrite H2. 
      unfold Parser.parseOutputPatternLink.
      unfold ConcreteSyntax.o_OutRefKind.
      unfold ConcreteSyntax.o_outpat.
      unfold ConcreteExpressions.makeLink.
      unfold ConcreteExpressions.wrapLink.
      unfold ConcreteExpressions.wrap.
      unfold ModelingMetamodel.toEData.
      simpl.
      unfold Moore.Transition_getTargetObject .

      specialize (MooreWF.getTransition_target_some m  WF_TLL s1 H0 t ) ; intro S.
      rewrite S.
      simpl.

      eapply TraceUtils.in_Resolve_trace_2 in H0.
      unfold ModelingSemantics.resolve.
      unfold ListUtils.singleton.
      rewrite H0.
      simpl.
      left.
      subst ; reflexivity.
      exact H.
    }
  }
  Unshelve. (* why ? *)
  exact 0.
Qed.

Lemma source_link_bw :
  forall t' s',
    In  
      (Mealy.TransitionSource {| left_glue := t' ; right_glue := s' |}) 
      (Semantics.execute Moore2Mealy m).(modelLinks) ->
    
    exists s, 
      Elements.convert_state s = s' 
      /\
        
        In 
          (Moore.TransitionSource 
             {|
               left_glue :=
                 Moore.Build_Transition_t t'.(Mealy.Transition_id) t'.(Mealy.Transition_input);
               right_glue := s
             |})
          m.(modelLinks).
Proof.
  intros t' s' IN.
  Tactics.exploit_link_in_result IN.
  { 
    PropUtils.inj IN0.
    PropUtils.inj EQ.
    simpl in IN_L.


    assert (S : SUCCESS (Moore.getTransition_target m t)).
    { apply WF_T. assumption. }
    destruct S as ( s2&GT).

    rewrite GT in IN_L. clear GT.
    simpl valueOption in IN_L.

    assert (S: SUCCESS (Moore.getTransition_source m t)).
    { apply WF_S. assumption. }
    destruct S as ( s1 & GS ).

    exists s1.
    unfold Moore.Transition_getSourceObject in IN_L.
    rewrite GS in IN_L.
    simpl in IN_L.


    OptionUtils.monadInv IN_L ; simpl.
    unfold ModelingSemantics.resolve in IN_L.
    unfold ModelingSemantics.denoteOutput in IN_L.
    PropUtils.destruct_match IN_L ; [ | discriminate IN_L].
    destruct t0 ; [ PropUtils.inj IN_L | discriminate IN_L].

    rename Heqo into R.

    unfold Resolve.maybeResolve in R.
    unfold Resolve.resolve in R.
    destruct (Certification.tr_resolveIter_leaf _ _ _ _ _ R) as (tk&?&? &?&?&?).
    clear R.

    apply Bool.Is_true_eq_true in H0.

    clear H1 H2. 

    apply ListUtils.list_beq_correct in H0 ; [ | exact Moore.internal_Element_dec_bl].

    destruct tk ; simpl in * ; subst.

    unfold ListUtils.singleton in H0.

    destruct source. destruct p. 

    unfold PoorTraceLink.getSourcePattern in H0 ;  simpl in H0.
    subst.

    apply Moore.getTransition_source_inv in GS. 

    destruct t as (id & i) ; simpl in *.
    split ; auto.
    

    Tactics.exploit_in_trace H.
    PropUtils.inj EQ.
    destruct t0 ; reflexivity.
  }
  
  { discriminate IN0. (* not the correct pattern. *)  }
Qed.

Lemma target_link_bw :
  forall t' s',
    In  
      (Mealy.TransitionTarget {| left_glue := t' ; right_glue := s' |}) 
      (Semantics.execute Moore2Mealy m).(modelLinks) ->
    
    exists s, 
      Elements.convert_state s = s' 
      /\
        
        In 
          (Moore.TransitionTarget 
             {|
               left_glue :=
                 Moore.Build_Transition_t t'.(Mealy.Transition_id) t'.(Mealy.Transition_input);
               right_glue := s
             |})
          m.(modelLinks).
Proof.
  intros t' s' IN.
  Tactics.exploit_link_in_result IN.
  { discriminate IN0. }
  { 
    PropUtils.inj IN0.
    PropUtils.inj EQ.
    simpl in IN_L.


    assert (S : SUCCESS (Moore.getTransition_target m t)).
    { apply WF_T. assumption. }
    destruct S as ( s2&GT).

    rewrite GT in IN_L. 
    simpl valueOption in IN_L.

    assert (S: SUCCESS (Moore.getTransition_source m t)).
    { apply WF_S. assumption. }
    destruct S as ( s1 & GS ).

    exists s2.
    unfold Moore.Transition_getTargetObject in IN_L.
    rewrite GT in IN_L.
    simpl in IN_L.



    OptionUtils.monadInv IN_L ; simpl.
    unfold ModelingSemantics.resolve in IN_L.
    unfold ModelingSemantics.denoteOutput in IN_L.
    PropUtils.destruct_match IN_L ; [ | discriminate IN_L].
    destruct t0 ; [ PropUtils.inj IN_L | discriminate IN_L].

    rename Heqo into R.

    unfold Resolve.maybeResolve in R.
    unfold Resolve.resolve in R.
    destruct (Certification.tr_resolveIter_leaf _ _ _ _ _ R) as (tk&?&? &?&?&?).
    clear R.

    apply Bool.Is_true_eq_true in H0.

    clear H1 H2. 

    apply ListUtils.list_beq_correct in H0 ; [ | exact Moore.internal_Element_dec_bl].

    destruct tk ; simpl in * ; subst.

    unfold ListUtils.singleton in H0.

    destruct source. destruct p. 

    unfold PoorTraceLink.getSourcePattern in H0 ;  simpl in H0.
    subst.

    apply Moore.getTransition_target_inv in GT. 

    destruct t as (id & i) ; simpl in *.
    split ; auto.
    
    Tactics.exploit_in_trace H.
    PropUtils.inj EQ.
    destruct t0 ; simpl. reflexivity. 
  }
  
Qed.

End Foo.
