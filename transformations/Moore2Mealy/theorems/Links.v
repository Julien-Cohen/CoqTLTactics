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

Hypothesis WF_U : MooreWF.unique_ids m.
Hypothesis WF_T : Moore.WF_target m.
Hypothesis WF_S : Moore.WF_source m.
Hypothesis WF_S_L : Moore.WF_source_lglue m.
Hypothesis WF_S_R : Moore.WF_source_rglue m.
Hypothesis WF_T_L : Moore.WF_target_lglue m.
Hypothesis WF_T_R : Moore.WF_target_rglue m.
Hypothesis WF_TLL : MooreWF.WF_targetLink_left m.
Hypothesis WF_SLL : MooreWF.WF_sourceLink_left m.

(* fixme : move-me *)
Lemma convert_transition_inv m0 :
  forall t t',
  Elements.convert_transition m0 t = Some t' ->
  exists s, Moore.getTransition_target m0 t = Some s /\  t'= {|
              Mealy.Transition_id := Moore.Transition_id t;
              Mealy.Transition_input := Moore.Transition_input t;
              Mealy.Transition_output := Moore.State_output s
            |}.

Proof.
  unfold Elements.convert_transition.
  intros  t t' H.
  PropUtils.destruct_match H ; [ PropUtils.inj H | discriminate H ].
  eauto.
Qed.



Lemma source_link_fw :
  forall t s1,
    In (Moore.Transition_sourceLink {| lglue := t ; rglue := s1 |}) m.(modelLinks) ->
    exists s2, 
      Moore.getTransition_target m t = Some s2 /\
        
        In  (Mealy.Transition_sourceLink 
    {|
      lglue :=
        {|
          Mealy.Transition_id := Moore.Transition_id t;
          Mealy.Transition_input := Moore.Transition_input t;
          Mealy.Transition_output := Moore.State_output s2
        |};
      rglue := Elements.convert s1
    |}) (Semantics.execute Moore2Mealy m).(modelLinks).
Proof.
  intros t s1 H.

  assert (In (Moore.StateElement s1) m.(modelElements)).
  {
    apply  WF_S_R in H. 
    assumption.
  }
  assert (In (Moore.TransitionElement t) m.(modelElements)).
  {
    apply  WF_S_L in H. 
    assumption.
  }
  destruct (Elements.convert_transition_ok _ WF_T _ H1) as (t' & T).
  destruct (convert_transition_inv _ _ _ T) as ( s2 & ?& ?).

  exists s2 ; split ; [assumption | ].

  specialize (TraceUtils.state_in_trace m s1 H0) ; intro INTRACE.




  eapply Tactics.in_links_fw with (tc:=Moore2MealyTransformationConfiguration).
  3:{
    (* only the second rule builds links. *)
    simpl. right. left. (* second rule *)
    reflexivity. (* fixme : make a tactic for that *)
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
    simpl. left. reflexivity. (* fixme : make a tactic for that. *)
  }
  { (* eval output pattern *)
    reflexivity.
  }


  { (* eval output pattern link *)
    (* the output patern in this rule has two link patterns. *)
    (* Transition sources are managed by the first link pattern. *)

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
    { (* first link pattern *) unfold In. left. reflexivity. }
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
      unfold Moore.Transition_getSourceObject .

      specialize (MooreWF.getTransition_source_some m  WF_SLL s1 H0 t H) ; intro S.
      rewrite S.
      simpl.


      eapply TraceUtils.in_maybeResolve_trace_2 in H0.
      unfold ModelingSemantics.maybeResolve.
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

Lemma source_link_fw_2 :
  forall t s1,
    In (Moore.Transition_sourceLink {| lglue := t ; rglue := s1 |}) m.(modelLinks) ->
    exists t', 
      Elements.convert_transition m t = Some t' /\
        In  (Mealy.Transition_sourceLink 
               {| lglue := t' ; rglue := Elements.convert s1 |})
           (Semantics.execute Moore2Mealy m).(modelLinks).
Proof.
  intros t s1 H ; apply source_link_fw in H.
  destruct H.
  destruct H.
  unfold Elements.convert_transition.
  rewrite H.
  eexists ; split ; auto.
Qed.

Lemma target_link_fw :
  forall t s1,
    In (Moore.Transition_targetLink {| lglue := t ; rglue := s1 |}) m.(modelLinks) ->
    exists s2, 
      Moore.getTransition_target m t = Some s2 /\
        
        In  (Mealy.Transition_targetLink 
    {|
      lglue :=
        {|
          Mealy.Transition_id := Moore.Transition_id t;
          Mealy.Transition_input := Moore.Transition_input t;
          Mealy.Transition_output := Moore.State_output s2
        |};
      rglue := Elements.convert s1
    |}) (Semantics.execute Moore2Mealy m).(modelLinks).
Proof.
  intros t s1 H.

  assert (In (Moore.StateElement s1) m.(modelElements)).
  {
    apply  WF_T_R in H. 
    assumption.
  }
  assert (In (Moore.TransitionElement t) m.(modelElements)).
  {
    apply  WF_T_L in H. 
    assumption.
  }
  destruct (Elements.convert_transition_ok _ WF_T _ H1) as (t' & T).
  destruct (convert_transition_inv _ _ _ T) as ( s2 & ?& ?).

  exists s2 ; split ; [assumption | ].

  specialize (TraceUtils.state_in_trace m s1 H0) ; intro INTRACE.




  eapply Tactics.in_links_fw with (tc:=Moore2MealyTransformationConfiguration).
  3:{
    (* only the second rule builds links. *)
    simpl. right. left. (* second rule *)
    reflexivity. (* fixme : make a tactic for that *)
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
    simpl. left. reflexivity. (* fixme : make a tactic for that. *)
  }
  { (* eval output pattern *)
    reflexivity.
  }


  { (* eval output pattern link *)
    (* the output patern in this rule has two link patterns. *)
    (* Transition sources are managed by the first link pattern. *)

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
    { (* second link pattern *) unfold In. right. left. reflexivity. }
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

      eapply TraceUtils.in_maybeResolve_trace_2 in H0.
      unfold ModelingSemantics.maybeResolve.
      unfold ListUtils.singleton.
      rewrite H0.
      simpl.
      left.
      reflexivity.
      exact H.
    }
  }
  Unshelve. (* why ? *)
  exact 0.
Qed.

Lemma target_link_fw_2 :
  forall t s1,
    In (Moore.Transition_targetLink {| lglue := t ; rglue := s1 |}) m.(modelLinks) ->
    exists t', 
      Elements.convert_transition m t = Some t' /\
        In  
          (Mealy.Transition_targetLink {| lglue := t' ; rglue := Elements.convert s1 |}) 
          (Semantics.execute Moore2Mealy m).(modelLinks).
Proof.
  intros t s1 H ; apply target_link_fw in H.
  destruct H.
  destruct H.
  unfold Elements.convert_transition.
  rewrite H.
  eexists ; split ; auto.
Qed.

End Foo.
