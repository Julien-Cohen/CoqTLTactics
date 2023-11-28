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



Lemma source_link_fw :
  forall t s1,
    In (Moore.TransitionSource (glue t with s1)) m.(modelLinks) ->
    exists t', 
      Moore2Mealy.convert_transition m t = Some t' /\
        In  (Mealy.TransitionSource 
               (glue t' with Moore2Mealy.convert_state s1 ))
           (Semantics.execute Moore2Mealy m).(modelLinks).
Proof.
  intros t s1 H.

  assert (IN_S : In (Moore.State s1) m.(modelElements)).
  { apply WF_S_R in H ; assumption. }

  assert (IN_T : In (Moore.Transition t) m.(modelElements)).
  { apply  WF_S_L in H ; assumption. }

  destruct (Elements.convert_transition_suff _ WF_T _ IN_T) as (t' & T).
 
  exists t' ; split ; [ assumption | ].

  specialize (TraceUtils.state_in_trace m s1 IN_S) ;
    intro IN_TRACE.

  apply <- Semantics.in_modelLinks_inv.
  setoid_rewrite Semantics.in_compute_trace_inv.
  repeat (first [eexists | split | eassumption]).
  
  
  { (* The source pattern is the considered transition *)
    apply ListUtils.incl_singleton. exact IN_T.
  }

  { (* arity *)
    compute. auto. }

  { (* Only the second rule builds links. *)
    TacticsFW.second_rule.
  }

  { (* eval guard *) reflexivity. }

  { (* eval iterator *) compute. eauto. }

  { (* output pattern *)
    (* This rule has one output pattern. *)    
    TacticsFW.first_in_list.
  }

  { (* eval output pattern *)
    simpl. 
    unfold ConcreteExpressions.makeElement.
    unfold ConcreteExpressions.wrapElement.
    simpl.
    rewrite T.
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

    apply in_flat_map.
    eexists ; split.
    { (* first link pattern *) apply in_eq. }
    {
      unfold ConcreteSyntax.o_OutRefKind, ConcreteSyntax.o_outpat.

      unfold ConcreteExpressions.makeLink, ConcreteExpressions.wrapLink, ConcreteExpressions.wrap,  ModelingMetamodel.toEData.
      simpl.
      unfold Moore.Transition_getSourceObject .

      specialize (MooreWF.getTransition_source_some m  WF_SLL s1 IN_S t H) ; intro S.
      rewrite S.
      simpl.


      eapply TraceUtils.in_model_resolve in IN_S.
      unfold ModelingSemantics.resolve. 
      unfold ListUtils.singleton.
      rewrite IN_S.
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
    In (Moore.TransitionTarget (glue t with s1)) m.(modelLinks) ->
    exists t', 
      Moore2Mealy.convert_transition m t = Some t' /\
        In  
          (Mealy.TransitionTarget (glue t' with Moore2Mealy.convert_state s1)) 
          (Semantics.execute Moore2Mealy m).(modelLinks).
Proof.
  intros t s1 H.

  assert (IN_S: In (Moore.State s1) m.(modelElements)).
  {
    apply  WF_T_R in H. 
    assumption.
  }
  assert (IN_T : In (Moore.Transition t) m.(modelElements)).
  {
    apply  WF_T_L in H. 
    assumption.
  }
  destruct (Elements.convert_transition_suff _ WF_T _ IN_T) as (t' & T).
  destruct (Elements.convert_transition_nec _ _ _ T) as ( s2 & ?& ?).

  exists t' ; split ; [assumption | ].

  specialize (TraceUtils.state_in_trace m s1 IN_S) ; intro INTRACE.

  apply <- Semantics.in_modelLinks_inv.
  setoid_rewrite Semantics.in_compute_trace_inv.
  repeat (first [eexists | split | eassumption]).
 
  3:{
    (* only the second rule builds links. *)
    TacticsFW.second_rule.
  }
  { 
    (* the source pattern is the considered transition *)
    apply ListUtils.incl_singleton.
    exact IN_T.
  }
  { (* arity *)
    compute ; auto. }
  { (* eval guard *) reflexivity. }
  { (* eval iterator *) compute. eauto. }
  { (* output pattern *)
    (* this rule has one output pattern *)
    TacticsFW.first_in_list.
  }
  { (* eval output pattern *)
    simpl.
    unfold ConcreteExpressions.makeElement.
    unfold ConcreteExpressions.wrapElement.
    simpl.
    rewrite T.
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
    { (* second link pattern *) TacticsFW.second_in_list. }
    {
      unfold Parser.parseOutputPatternLink.
      unfold ConcreteSyntax.o_OutRefKind.
      unfold ConcreteSyntax.o_outpat.
      unfold ConcreteExpressions.makeLink.
      unfold ConcreteExpressions.wrapLink.
      unfold ConcreteExpressions.wrap.
      unfold ModelingMetamodel.toEData.
      simpl.
      unfold Moore.Transition_getTargetObject .

      specialize (MooreWF.getTransition_target_some m  WF_TLL s1 IN_S t ) ; intro S.
      rewrite S.
      simpl.

      eapply TraceUtils.in_model_resolve in IN_S.
      unfold ModelingSemantics.resolve.
      unfold ListUtils.singleton.
      rewrite IN_S.
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
      (Mealy.TransitionSource (glue t' with s')) 
      (Semantics.execute Moore2Mealy m).(modelLinks) ->
    
    exists s, 
      Moore2Mealy.convert_state s = s' 
      /\
        
        In 
          (Moore.TransitionSource 
             (glue 
                 Moore.Build_Transition_t t'.(Mealy.Transition_id) t'.(Mealy.Transition_input)
               with s)
          )
          m.(modelLinks).
Proof.
  intros t' s' IN.
  TacticsBW.exploit_link_in_result IN.
  { 
    PropUtils.inj IN0.
    simpl in IN_L.



    monadInv IN_L.
    monadInv IN_L.

    compute in EQ0.
    PropUtils.inj EQ0.


    assert (S: SUCCESS (Moore.getTransition_source m t)).
    { apply WF_S. assumption. }
    destruct S as ( s1 & GS ).

    exists s1.
    unfold Moore.Transition_getSourceObject in EQ1.
    rewrite GS in EQ1.
    simpl in EQ1.
    PropUtils.inj EQ1.

    unfold ModelingSemantics.resolve in IN_L.
    unfold ModelingSemantics.denoteOutput in IN_L.
    monadInv IN_L.
    compute in IN_L.
    
    destruct t0 ; [ PropUtils.inj IN_L | discriminate IN_L].

    rename EQ0 into R.

    unfold Resolve.resolve in R.
    destruct (Certification.tr_resolveIter_leaf _ _ _ _ _ R) as (tk&?&? &?&?&?).
    clear R.

    apply Bool.Is_true_eq_true in H0.

    clear H1 H2. 

    apply ListUtils.list_beq_correct in H0 ; [ | exact Moore.internal_Element_dec_bl].

    destruct tk ; simpl in * ; subst.

    unfold ListUtils.singleton in H0.

    destruct source. destruct p. 

    unfold PoorTraceLink.getSourcePiece in H0 ;  simpl in H0.
    subst.

    apply Moore.getTransition_source_inv in GS. 

    compute in t.

    unfold convert_transition in EQ.
    monadInv EQ.
    destruct t as (id & i) ; simpl in *.

    TacticsBW.exploit_in_trace H.
    
    split ; [ reflexivity | ].
    exact GS.

  }
  
  { discriminate IN0. (* not the correct pattern. *)  }
Qed.

Lemma target_link_bw :
  forall t' s',
    In  
      (Mealy.TransitionTarget (glue t' with s')) 
      (Semantics.execute Moore2Mealy m).(modelLinks) ->
    
    exists s, 
      Moore2Mealy.convert_state s = s' 
      /\
        
        In 
          (Moore.TransitionTarget 
             (glue 
                 Moore.Build_Transition_t t'.(Mealy.Transition_id) t'.(Mealy.Transition_input) 
               with s)
          )
          m.(modelLinks).
Proof.
  intros t' s' IN.
  TacticsBW.exploit_link_in_result IN.
  { discriminate IN0. }
  { 
    PropUtils.inj IN0.
    simpl in IN_L.
    monadInv IN_L.
    monadInv IN_L.
    compute in EQ0. PropUtils.inj EQ0.
    
    compute in t.

    unfold convert_transition in EQ. monadInv EQ.
    simpl.

    assert (S: SUCCESS (Moore.getTransition_source m t)).
    { apply WF_S. assumption. }
    destruct S as ( s1 & GS ).

    exists s.
    unfold Moore.Transition_getTargetObject in EQ1.
    rewrite EQ in EQ1.
    simpl in EQ1. PropUtils.inj EQ1.
    
    unfold ModelingSemantics.resolve in IN_L.
    unfold ModelingSemantics.denoteOutput in IN_L.
    monadInv IN_L. compute in IN_L. 
    
    destruct t0 ; [ PropUtils.inj IN_L | discriminate IN_L].

    rename EQ0 into R.

    unfold Resolve.resolve in R.
    destruct (Certification.tr_resolveIter_leaf _ _ _ _ _ R) as (tk&?&? &?&?&?).
    clear R.

    apply Bool.Is_true_eq_true in H0.

    clear H1 H2. 

    apply ListUtils.list_beq_correct in H0 ; [ | exact Moore.internal_Element_dec_bl].

    destruct tk ; simpl in * ; subst.

    unfold ListUtils.singleton in H0.

    destruct source. destruct p. 

    unfold PoorTraceLink.getSourcePiece in H0 ;  simpl in H0.
    subst.

    apply Moore.getTransition_target_inv in EQ.

    TacticsBW.exploit_in_trace H ; [].

    simpl in *.
    split ; [ reflexivity | ].
    destruct t as (id & i) ; simpl in *.
    exact EQ.
  }
  
Qed.

End Foo.
