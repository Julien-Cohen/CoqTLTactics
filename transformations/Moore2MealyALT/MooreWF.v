
Require Import Moore2MealyALT.Moore Moore2MealyALT.MooreSemantics. 
Import String.
Import Id.

Definition unique_ids (m:Moore.M) := 
  forall e1 e2,
    List.In (StateElement e1) m.(Model.modelElements) ->
    List.In (StateElement e2) m.(Model.modelElements) ->
    e1.(State_id) = e2.(State_id) ->
    e1 = e2.



Lemma discr  (m : M) : 
  unique_ids m ->
  forall (i : NodeId),
    ListUtils.discriminating_predicate
      (fun x => NodeId_beq i (State_id x) = true)
      (OptionListUtils.lift_list (get_E_data State_K)
         (Model.modelElements m)).
Proof.
  intros WF i.
  unfold ListUtils.discriminating_predicate ; intros.
  apply WF.
  apply In_state ; assumption.
  apply In_state ; assumption.
  apply internal_NodeId_dec_bl in H1, H2.
  congruence.
Qed.


Lemma in_find : 
  forall m n e,
    unique_ids m ->
    List.In (StateElement e) m.(Model.modelElements) ->
    e.(State_id) = n ->
    find_State
           (fun s => NodeId_beq n  s.(State_id))
           m.(Model.modelElements) = 
         Some e.
Proof.
  intros.
  eapply OptionListUtils.in_find_lift ; [ | | | exact H0 ].
  { apply discr. assumption. }
  { reflexivity. }
  { apply internal_NodeId_dec_lb. auto. }  
Qed.



Lemma getTransition_source_some (m:Moore.M) :
  unique_ids m ->
  forall s,
    List.In (StateElement s) m.(Model.modelElements) ->
    forall t,
      State_id s = t.(Transition_source) ->
      getTransition_source m t = Some s. 
Proof.
  intros WF s H1 t H2.
  unfold getTransition_source.
  eapply OptionListUtils.in_find_lift ; [ | | | exact H1 ].
  { apply discr. assumption. }
  { reflexivity. }
  { apply internal_NodeId_dec_lb. auto. }  
Qed.

Lemma getTransition_target_some (m:Moore.M) :
  unique_ids m ->  
  forall s, 
    List.In (StateElement s) m.(Model.modelElements) ->
    forall t,
      State_id s = t.(Transition_dest) ->
      getTransition_target m t = Some s. 
Proof.
  intros WF s H1 t H2.
  unfold getTransition_target.
  eapply OptionListUtils.in_find_lift ; [ | | | exact H1 ].
  { apply discr. assumption. }
  { reflexivity. }
  { apply internal_NodeId_dec_lb. auto. }  
Qed.
 

(** Each node has only one transition getting out of it for a same input. *)
Definition determinist (m:Moore.M) := 
  forall t1 t2,
      List.In (TransitionElement t1) m.(Model.modelElements)->
      List.In (TransitionElement t2) m.(Model.modelElements)->
      t1.(Transition_source) = t2.(Transition_source) ->
      t1.(Transition_input) = t2.(Transition_input) ->
      t1 = t2.


Lemma truc m :
  determinist m ->
  forall s i,
    ListUtils.discriminating_predicate
      (fun x : Transition_t =>
         (i =? Transition_input x)%string = true)
      (MooreSemantics.State_outTransitions m s).
Proof.
  intro WF.
  intros s i.
  intros t1 t2 H1 H2 P1 P2.
  unfold State_outTransitions in H1, H2.
  apply OptionListUtils.filter_lift_in in H1, H2.
  destruct H1 as ( ? & ? & ? & ?).
  destruct H2 as ( ? & ? & ? & ?).
  PropUtils.destruct_match_H H1 ; [ | discriminate H1].
  PropUtils.destruct_match_H H4 ; [ | discriminate H4].
  destruct x ; [ discriminate H0 | PropUtils.inj H0]. (* monadInv *)
  destruct x0 ; [ discriminate H3 | PropUtils.inj H3]. (* monadInv *)
  apply internal_State_t_dec_bl in H1, H4.
  subst s1 s0.
  apply WF ; auto ; [ | ].
  {
    apply getTransition_source_inv in Heqo, Heqo0.
    destruct Heqo.
    destruct Heqo0.
    congruence.
  }
  {
    apply String.eqb_eq in P1.
    apply String.eqb_eq in P2.
    congruence.
  }
Qed.
