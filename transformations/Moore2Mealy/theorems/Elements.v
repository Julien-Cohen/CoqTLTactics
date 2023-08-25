Require Moore2Mealy.MooreSemantics.
Require Moore2Mealy.MealySemantics.
Require Moore2Mealy.Moore2Mealy.
Require Moore2Mealy.MooreWF.
Require Moore2Mealy.MealyWF.

Import OptionUtils.

Section Params.

Variable (m:Moore.M).

Hypothesis WF_U : MooreWF.state_id_uniqueness m.
Hypothesis WF_T : Moore.WF_transition_target_exists m.

Definition convert_state (s:Moore.State_t) : Mealy.State_t :=
  {| Mealy.State_id := s.(Moore.State_id) |}.

(** [convert_state] is not injective, but if we consider states of a model with uniqueness of identifiers, it becomes injective. *)

Lemma convert_state_injective : 
  forall s1 s2,
    List.In (Moore.State s1) m.(Model.modelElements) ->
    List.In (Moore.State s2) m.(Model.modelElements) ->
    convert_state s1 = convert_state s2 ->
    s1 = s2.
Proof.
  intros s1 s2 H1 H2 H3.
  apply WF_U ; auto.
  destruct s1, s2 ; unfold convert_state in H3 ; congruence.
Qed.


Definition convert_transition  (t : Moore.Transition_t) : option Mealy.Transition_t :=
  match Moore.getTransition_target m t with
  | None => None
  | Some s => Some (Mealy.Build_Transition_t t.(Moore.Transition_id) t.(Moore.Transition_input) s.(Moore.State_output))
  end.


Lemma convert_transition_injective : 
  forall t1 t2 a, 
    convert_transition t1 = Some a -> (* would be false with None *)
    convert_transition t2 = Some a ->
    t1 = t2.
Proof.
  unfold convert_transition ; intros.
  PropUtils.destruct_match H ; [ PropUtils.inj H | discriminate H].
  PropUtils.destruct_match H0 ; [ PropUtils.inj H0 | discriminate H0].
  
  destruct t1, t2 ; simpl in * ; congruence.
Qed.


Lemma convert_transition_suff : forall t,
    List.In (Moore.Transition t) m.(Model.modelElements) -> 
    SUCCESS (convert_transition t).
Proof.
  intros t H.
  apply WF_T in H.
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

Lemma convert_transition_nec :
  forall t t',
  convert_transition t = Some t' ->
  exists s, 
    Moore.getTransition_target m t = Some s
    /\  t'= {|
              Mealy.Transition_id := Moore.Transition_id t;
              Mealy.Transition_input := Moore.Transition_input t;
              Mealy.Transition_output := Moore.State_output s
            |}.
Proof.
  unfold convert_transition.
  intros  t t' H.
  PropUtils.destruct_match H ; [ PropUtils.inj H | discriminate H ].
  eauto.
Qed.


(* Just to try *)
Definition convert_transition' t (IN : List.In (Moore.Transition t) m.(Model.modelElements)) : Mealy.Transition_t .
  destruct (Moore.getTransition_target m t) eqn:G.
  + exact (Mealy.Build_Transition_t t.(Moore.Transition_id) t.(Moore.Transition_input) s.(Moore.State_output)).
  + exfalso.
    apply convert_transition_suff in IN.
    unfold convert_transition in IN.
    rewrite G in IN.
    inversion IN.
    discriminate H.
Defined.

Notation transform_element_fw := 
  (Tactics.transform_element_fw  (tc := Moore2Mealy.Moore2MealyTransformationConfiguration)).

Lemma state_element_fw : 
  forall (s:Moore.State_t),
    List.In (Moore.State s) (Model.modelElements m) ->
    List.In (Mealy.State (convert_state s))  (Semantics.execute  Moore2Mealy.Moore2Mealy m).(Model.modelElements).
Proof.
  intros s IN.
  eapply transform_element_fw ; eauto. 
  compute ; auto.
Qed.

Lemma state_element_bw :
  forall (s:Mealy.State_t),
    List.In (Mealy.State s) (Model.modelElements (Semantics.execute  Moore2Mealy.Moore2Mealy m)) ->
    exists s0,
      List.In (Moore.State s0) (Model.modelElements m) /\ s = convert_state s0.
Proof.
  intros s H.
  core.Tactics.exploit_element_in_result H.
  exists t0.
  split ; auto.
Qed.

End Params.
