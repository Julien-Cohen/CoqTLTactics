Require Moore2Mealy.MooreSemantics.
Require Moore2Mealy.MealySemantics.
Require Moore2Mealy.Moore2Mealy.
Require Moore2Mealy.MooreWF.
Require Moore2Mealy.MealyWF.

Import OptionUtils.

Definition convert (s:Moore.State_t) : Mealy.State_t :=
  {| Mealy.State_id := s.(Moore.State_id) |}.

Definition convert_transition  (m: Moore.M)  (t : Moore.Transition_t)   :option Mealy.Transition_t :=
  match Moore.getTransition_target m t with
  | None => None
  | Some s => Some (Mealy.Build_Transition_t t.(Moore.Transition_id) t.(Moore.Transition_input) s.(Moore.State_output))
  end.

Lemma convert_transition_ok : forall (m:Moore.M) t,
    Moore.WF1 m ->
    List.In (Moore.TransitionElement t) m.(Model.modelElements) -> 
    SUCCESS (convert_transition m t).
Proof.
  intros m t H0 H.
  apply H0 in H.
  destruct H as [s H].
  unfold convert_transition.
  exists (Mealy.Build_Transition_t t.(Moore.Transition_id) t.(Moore.Transition_input) s.(Moore.State_output)).
  simpl.
  destruct t.
  Tactics.destruct_match.
  + PropUtils.inj H.
    reflexivity.
  + discriminate.
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

