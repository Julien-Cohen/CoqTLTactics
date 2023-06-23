Require Moore2MealyALT.MooreSemantics.
Require Moore2MealyALT.MealySemantics.
Require Moore2MealyALT.Moore2Mealy.
Require Moore2MealyALT.MooreWF.
Require Moore2MealyALT.MealyWF.

Import String OptionUtils.

Definition convert (s:Moore.State_t) : Mealy.State_t :=
  {| Mealy.State_name := s.(Moore.State_name) |}.

Definition convert_transition  (m: Moore.M)  (t : Moore.Transition_t)   :option Mealy.Transition_t :=
  match Moore.getTransition_target m t with
  | None => None
  | Some s => Some (Mealy.Build_Transition_t t.(Moore.Transition_source) t.(Moore.Transition_input) s.(Moore.State_output) t.(Moore.Transition_dest))
  end.

Lemma convert_transition_ok : forall (m:Moore.M) t,
    Moore.WF_target m ->
    List.In (Moore.TransitionElement t) m.(Model.modelElements) -> 
    SUCCESS (convert_transition m t).
Proof.
  intros m t H0 H.
  apply H0 in H.
  destruct H as [s H].
  unfold convert_transition.
  exists (Mealy.Build_Transition_t t.(Moore.Transition_source) t.(Moore.Transition_input) s.(Moore.State_output) t.(Moore.Transition_dest)).
  rewrite H.
  reflexivity.
Qed.  

Lemma convert_transition_inv m t t':
  convert_transition m t = Some t' ->
  exists s,
  Moore.getTransition_target m t = Some s /\ t' ={|
    Mealy.Transition_source := Moore.Transition_source t;
    Mealy.Transition_input := Moore.Transition_input t;
    Mealy.Transition_output := Moore.State_output s;
    Mealy.Transition_dest := Moore.Transition_dest t
  |}.
Proof.    
  unfold Elements.convert_transition ; intro.
  PropUtils.destruct_match H ; [ PropUtils.inj H | discriminate H].
  eauto.
Qed.

Lemma state_element_fw : 
  forall (s:Moore.State_t) (m:Moore.M),
    List.In (Moore.StateElement s) (Model.modelElements m) ->
    List.In (Mealy.StateElement (convert s))  (Semantics.execute  Moore2Mealy.Moore2Mealy m).(Model.modelElements).
Proof.
  intros s m IN.
  eapply Tactics.in_modelElements_execute_left.
  + apply Certification.allTuples_incl_length.
    apply ListUtils.incl_singleton.
    exact IN.
    compute ; auto.
  + apply List.in_eq. (* first rule *)
  + reflexivity.
  + compute. left. reflexivity.
  + apply List.in_eq. 
  + destruct s.
    simpl.
    reflexivity.
Qed.

Lemma state_element_bw :
  forall (s:Mealy.State_t) (m:Moore.M),
    List.In (Mealy.StateElement s) (Model.modelElements (Semantics.execute  Moore2Mealy.Moore2Mealy m)) ->
    exists s0,
      List.In (Moore.StateElement s0) (Model.modelElements m) /\ s = convert s0.
Proof.
  intros s m H.
  core.Tactics.exploit_element_in_result H.
  exists t0.
  split ; auto.
Qed.

Lemma transition_element_bw :
  forall (t:Mealy.Transition_t) (m:Moore.M),
    Moore.WF_target m ->
    List.In (Mealy.TransitionElement t) (Model.modelElements (Semantics.execute  Moore2Mealy.Moore2Mealy m)) ->
    exists t0,
      List.In (Moore.TransitionElement t0) (Model.modelElements m) /\ Some t = convert_transition m t0.
Proof.
  intros t m WF H.
  core.Tactics.exploit_element_in_result H.
  exists t1.
  split ; auto ; [].
  apply WF in IN_ELTS.
  destruct IN_ELTS as (s & G).
  (* FIXME : ici on voit valueOption, c'est moche. *)
  unfold convert_transition.
  rewrite G.
  reflexivity.
Qed.

Lemma transition_element_fw : 
  forall (t:Moore.Transition_t) (m:Moore.M),
    Moore.WF_target m ->
    List.In (Moore.TransitionElement t) (Model.modelElements m) ->
    exists t', 
      convert_transition m t = Some t' /\
        List.In (Mealy.TransitionElement t')  (Semantics.execute  Moore2Mealy.Moore2Mealy m).(Model.modelElements).
Proof.
  intros t m WF IN.
  destruct (WF _ IN) as (s & G).
  unfold convert_transition.
  rewrite G.
  eexists ; split ; [ reflexivity| ].
  eapply Tactics.in_modelElements_execute_left.
  + apply Certification.allTuples_incl_length.
    apply ListUtils.incl_singleton.
    exact IN.
    compute ; auto.
  + apply List.in_cons. apply List.in_eq. (* second rule *)
  + reflexivity.
  + compute. left. reflexivity.
  + apply List.in_eq. 
  + destruct s.
    simpl.
    unfold ConcreteExpressions.makeElement.
    unfold ConcreteExpressions.wrapElement. simpl.
    rewrite G.
    reflexivity.
Qed.
