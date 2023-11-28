Require Moore2MealyALT.MooreSemantics.
Require Moore2MealyALT.MealySemantics.
Require Import Moore2MealyALT.Moore2Mealy.
Require Moore2MealyALT.MooreWF.
Require Moore2MealyALT.MealyWF.

Require core.TacticsFW core.TacticsBW.

Import String OptionUtils.

Section Foo.

Variable (m:Moore.M).

Hypothesis WF_U : MooreWF.unique_ids m.
Hypothesis WF_T : Moore.WF_target m.

Definition convert_state (s:Moore.State_t) : Mealy.State_t :=
  {| Mealy.State_id := s.(Moore.State_id) |}.

(** [convert_state] is not injective, but if we consider states of a model with uniqueness of identifiers, it becomes injective. *)
Lemma convert_state_injective : 
  forall s1 s2,
    List.In (Moore.StateElement s1) m.(Model.modelElements) ->
    List.In (Moore.StateElement s2) m.(Model.modelElements) ->
    convert_state s1 = convert_state s2 ->
    s1 = s2.
Proof.
  intros s1 s2 H1 H2 H3.
  apply WF_U ; auto.
  destruct s1, s2 ; unfold convert_state in H3 ; congruence.
Qed.


Definition convert_transition  (t : Moore.Transition_t)   :option Mealy.Transition_t :=
  match Moore.getTransition_target m t with
  | None => None
  | Some s => Some (Mealy.Build_Transition_t t.(Moore.Transition_source) t.(Moore.Transition_input) s.(Moore.State_output) t.(Moore.Transition_dest))
  end.


Lemma convert_transition_injective : 
  forall t1 t2 a, 
    convert_transition t1 = Some a -> 
    convert_transition t2 = Some a ->
    t1 = t2.
Proof.
  unfold convert_transition ; intros.
  PropUtils.destruct_match_H H ; [ PropUtils.inj H | discriminate H].
  PropUtils.destruct_match_H H0 ; [ PropUtils.inj H0 | discriminate H0].
  
  destruct t1, t2 ; simpl in * ; congruence.
Qed.

(* not used *)
Lemma convert_transition_suff : forall t,
    List.In (Moore.TransitionElement t) m.(Model.modelElements) -> 
    SUCCESS (convert_transition t).
Proof.
  intros t H.
  apply WF_T in H.
  destruct H as [s H].
  unfold convert_transition.
  exists (Mealy.Build_Transition_t t.(Moore.Transition_source) t.(Moore.Transition_input) s.(Moore.State_output) t.(Moore.Transition_dest)).
  rewrite H.
  reflexivity.
Qed.  

Lemma convert_transition_ok2 : forall t,
    List.In (Moore.TransitionElement t) m.(Model.modelElements) -> 
    exists s,
      Moore.getTransition_target m t = Some s /\
        convert_transition t = 
          Some (Mealy.Build_Transition_t 
                  t.(Moore.Transition_source) 
                      t.(Moore.Transition_input) 
                          s.(Moore.State_output) 
                              t.(Moore.Transition_dest)).
Proof.
  intros t H.
  apply WF_T in H.
  destruct H as [s H].
  exists s.
  split ; [assumption | ].
  unfold convert_transition.
  rewrite H.
  reflexivity.
Qed.  

Lemma convert_transition_nec t t':
  convert_transition t = Some t' ->
  exists s,
  Moore.getTransition_target m t = Some s /\ 
    t' ={|
     Mealy.Transition_source := Moore.Transition_source t;
     Mealy.Transition_input := Moore.Transition_input t;
     Mealy.Transition_output := Moore.State_output s;
     Mealy.Transition_dest := Moore.Transition_dest t
  |}.
Proof.    
  unfold convert_transition ; intro.
  PropUtils.destruct_match_H H ; [ PropUtils.inj H | discriminate H].
  eauto.
Qed.

Notation transform_element_fw := 
  (TacticsFW.transform_element_fw  (tc := Moore2Mealy.Moore2MealyTransformationConfiguration)).

Lemma state_element_fw : 
  forall (s:Moore.State_t),
    List.In (Moore.StateElement s) (Model.modelElements m) ->
    List.In (Mealy.StateElement (convert_state s))  (Semantics.execute  Moore2Mealy.Moore2Mealy m).(Model.modelElements).
Proof.
  intros s IN.
  eapply transform_element_fw ; eauto. 
  compute ; auto.
Qed.

Lemma state_element_bw :
  forall (s:Mealy.State_t),
    List.In (Mealy.StateElement s) (Model.modelElements (Semantics.execute  Moore2Mealy.Moore2Mealy m)) ->
    exists s0,
      List.In (Moore.StateElement s0) (Model.modelElements m) /\ s = convert_state s0.
Proof.
  intros s H.
  TacticsBW.exploit_element_in_result H.
  compute in t0.
  exists t0.
  split ; auto.
Qed.

Lemma transition_element_bw :
  forall (t:Mealy.Transition_t),
    List.In (Mealy.TransitionElement t) (Model.modelElements (Semantics.execute  Moore2Mealy.Moore2Mealy m)) ->
    exists t0,
      List.In (Moore.TransitionElement t0) (Model.modelElements m) /\ Some t = convert_transition t0.
Proof.
  intros t H.
  TacticsBW.exploit_element_in_result H.
  exists t1.
  split ; auto ; [].
  apply WF_T in IN_ELTS0.
  destruct IN_ELTS0 as (s & G).
  (* FIXME : ici on voit valueOption, c'est moche. *)
  unfold convert_transition.
  rewrite G.
  reflexivity.
Qed.


Lemma transition_element_fw : 
  forall (t:Moore.Transition_t),
    List.In (Moore.TransitionElement t) (Model.modelElements m) ->
    exists t', 
      convert_transition t = Some t' /\
        List.In (Mealy.TransitionElement t')  (Semantics.execute  Moore2Mealy.Moore2Mealy m).(Model.modelElements).
Proof.
  intros t IN.
  destruct (WF_T _ IN) as (s & G).
  unfold convert_transition.
  rewrite G.
  eexists ; split ; [ reflexivity| ].
  eapply transform_element_fw ; eauto.
  (* Here we would like to "compute", but we have to do the [rewrite G] below. *)
  simpl.
  rewrite G.
  auto.
Qed.

End Foo.
