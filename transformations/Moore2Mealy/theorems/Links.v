From transformations.Moore2Mealy 
       Require MooreSemantics MealySemantics Moore2Mealy MooreWF MealyWF.

From transformations.Moore2Mealy.theorems 
  Require Elements TraceUtils.

From usertools 
  Require ResolveTools. (* Other usertools come from Require Elements *)

Import
  OptionUtils List String (* for notation *) Model Glue Moore2Mealy.


Section Foo.

Variable (m:Moore.M).

Hypothesis WF_U : MooreWF.state_id_uniqueness m.
Hypothesis WF_T : Moore.WF_transition_target_exists m.
Hypothesis WF_S : Moore.WF_transition_source_exists m.
Hypothesis WF_S_L : Moore.WF_transition_source_glue_l_exists m.
Hypothesis WF_S_R : Moore.WF_transition_source_glue_r_exists m.
Hypothesis WF_T_L : Moore.WF_transition_target_glue_l_exists m.
Hypothesis WF_T_R : Moore.WF_transition_target_glue_r_exists m.
Hypothesis WF_TLL : MooreWF.WF_transition_target_uniqueness m.
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


  (* Remark : the FW tactic below works if we invert the position of IN_S and IN_T in the context, thanks to the use of multimatch in the tactic. Comment/uncomment the following line to explore this. *)
  move IN_T after IN_S.

  (*  TacticsFW.transform_link_fw_tac_singleton 2 1 0 ; [ | ].*) 
  TacticsFW.transform_link_fw_tac_singleton_auto 0. 

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
      ConcreteSyntax.e_outpat,
      ConcreteSyntax.e_name,
      Syntax.opu_name.
    
    unfold Parser.dropToList,
      Parser.parseOutputPatternLinks, 
      Parser.parseOutputPatternLink.
    unfold  OptionListUtils.optionListToList.

    simpl ModelingMetamodel.constructor.

    apply in_flat_map.
    eexists ; split.
    { (* first link pattern *) ChoiceTools.first_in_list. }
    {
      unfold ConcreteSyntax.o_OutRefKind, ConcreteSyntax.o_outpat.

      unfold ConcreteExpressions.makeLink, ConcreteExpressions.wrapLink, ConcreteExpressions.wrap,  ModelingMetamodel.toEData.
      simpl.

      replace (Moore.Transition_getSourceObject t m) with (Some (Moore.State s1)).
      {
        simpl.
        eapply TraceUtils.in_model_resolve in IN_S.
        unfold ModelingSemantics.resolve. 
        unfold ListUtils.singleton.
        rewrite IN_S.
        simpl.
        left.
        reflexivity.
      }
      { 
        unfold Moore.Transition_getSourceObject .
        apply (MooreWF.getTransition_source_some m  WF_SLL s1 IN_S t) in  H.  rewrite H. reflexivity.
      }
    }
  }
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

  (*  TacticsFW.transform_link_fw_tac_singleton 2 1 0 ; [ | ].*)
  TacticsFW.transform_link_fw_tac_singleton_auto  0 ; [ | ].

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

    unfold UserExpressions.evalOutputPatternLink.
    unfold ConcreteSyntax.r_InKinds.
    unfold Parser.dropToList.
    apply OptionListUtils.in_optionListToList.
    eexists ; split ; [ reflexivity| ].
    apply in_flat_map.
    eexists ; split.
    { (* second link pattern *) ChoiceTools.second_in_list. }
    {
      unfold TraceLink.getSourcePiece, 
        TraceLink.getIteration, 
        TraceLink.source, 
        TraceLink.produced.
      unfold ConcreteSyntax.o_OutRefKind, 
        ConcreteSyntax.o_outpat.
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
                 {| 
                   Moore.Transition_id := t'.(Mealy.Transition_id) ; 
                   Moore.Transition_input := t'.(Mealy.Transition_input)
                 |}
               with s)
          )
          m.(modelLinks).
Proof.
  intros t' s' IN.
  TacticsBW.exploit_link_in_result IN.

    (* Exploit EQ0 *)
    PropUtils.inj EQ0.

    assert (S: SUCCESS (Moore.getTransition_source m t)).
    { apply WF_S. assumption. }
    destruct S as ( s1 & GS ).

    exists s1.
    unfold Moore.Transition_getSourceObject in EQ1.
    rewrite GS in EQ1.
    PropUtils.inj EQ1.

    (* Exploit IN_L) *)
    unfold ModelingSemantics.resolve in IN_L.
    unfold ModelingSemantics.denoteOutput in IN_L.
    monadInv IN_L.
    rename EQ0 into R.    
    compute in IN_L.
    
    destruct t0 ; [ PropUtils.inj IN_L | discriminate IN_L].

    (* Exploit resolve *)
    apply ResolveTools.tr_resolve_leaf in R. 
    
    apply Moore.getTransition_source_inv in GS. 
    
    compute in t.
    
    unfold convert_transition in EQ.
    monadInv EQ.

    destruct t as (id & i) ; simpl in *.

    TacticsBW.exploit_in_trace R.
    
    split ; [ | exact GS].
    PropUtils.inj E0.
    reflexivity.
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
                 {| Moore.Transition_id:= t'.(Mealy.Transition_id) ; Moore.Transition_input := t'.(Mealy.Transition_input) |} 
               with s)
          )
          m.(modelLinks).
Proof.
  intros t' s' IN.
  TacticsBW.exploit_link_in_result IN ; [].

  (* Exploit EQ0 *)
  PropUtils.inj EQ0.
  
  compute in t.

  (* Exploit EQ. *)
  unfold convert_transition in EQ. monadInv EQ.
  simpl.
  
  exists s.
  
  (* Exploit EQ1 *)
  unfold Moore.Transition_getTargetObject in EQ1.
  rewrite EQ in EQ1.
  PropUtils.inj EQ1.
  
  (* Exploit IN_L *)
  unfold ModelingSemantics.resolve in IN_L.
  unfold ModelingSemantics.denoteOutput in IN_L.
  monadInv IN_L. 
  rename EQ0 into R.
  compute in IN_L. 
  
  PropUtils.destruct_match_H IN_L ; [ PropUtils.inj IN_L | discriminate IN_L].
  
  (* Exploit resolve *)
  apply ResolveTools.tr_resolve_leaf in R.
  
  apply Moore.getTransition_target_inv in EQ.
  
  TacticsBW.exploit_in_trace R ; [].
  PropUtils.inj E0.
  split ; [ reflexivity | ].
  destruct t as (id & i) ; simpl.
  exact EQ.
Qed.


End Foo.
