
Require Import Moore2MealyALT.Moore Moore2MealyALT.MooreSemantics. 
Import String.
Import Id.

Definition unique_ids (m:Moore.M) := 
  forall e1 e2,
    List.In (StateElement e1) m.(Model.modelElements) ->
    List.In (StateElement e2) m.(Model.modelElements) ->
    e1.(State_id) = e2.(State_id) ->
    e1 = e2.

Lemma In_state : forall (m:Moore.M) e,
         List.In (StateElement e) (Model.modelElements m) <-> List.In e
    (OptionListUtils.lift_list (get_E_data State_K)
       (Model.modelElements m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (StateElement e). auto.
  }  
  {
    apply OptionListUtils.In_lift in H.
    destruct H as (e2 & (G & IN2)).
    destruct e2 ; [ PropUtils.inj G| discriminate G]. 
    assumption.
  }
Qed.

Lemma In_transition : forall (m:Moore.M) e,
         List.In (TransitionElement e) (Model.modelElements m) <-> List.In e
    (OptionListUtils.lift_list (get_E_data Transition_K)
       (Model.modelElements m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (TransitionElement e). auto.
  }  
  {
    apply OptionListUtils.In_lift in H.
    destruct H as (e2 & (G & IN2)).
    destruct e2 ; [ discriminate G | PropUtils.inj G]. 
    assumption.
  }
Qed.


Lemma discr  (m : M) : 
  unique_ids m ->
  forall (i : NodeId),
    ListUtils.discriminating_predicate
      (fun x : State_t => NodeId_beq i (State_id x) = true)
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
    OptionListUtils.find_lift (get_E_data State_K)
           (fun s : State_t => (NodeId_beq n  s.(State_id)))
           m.(Model.modelElements) = 
         Some e.
Proof.
  intros.
  eapply OptionListUtils.in_find_lift ; [ | | | exact H0 ].
  { apply discr. assumption. }
  { reflexivity. }
  { apply internal_NodeId_dec_lb. auto. }  
Qed.



Lemma getTransition_source_some (s:State_t) t (m:Moore.M) :
  unique_ids m ->
  List.In (StateElement s) m.(Model.modelElements) ->
  State_id s = t.(Transition_source) ->
  getTransition_source m t = Some s. 
Proof.
  intros WF H1 H2.
  unfold getTransition_source.
  eapply OptionListUtils.in_find_lift ; [ | | | exact H1 ].
  { apply discr. assumption. }
  { reflexivity. }
  { apply internal_NodeId_dec_lb. auto. }  
Qed.
 
Lemma getTransition_target_some (s:State_t) t (m:Moore.M) :
  unique_ids m ->
  List.In (StateElement s) m.(Model.modelElements) ->
  State_id s = t.(Transition_dest) ->
  getTransition_target m t = Some s. 
Proof.
  intros WF H1 H2.
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
