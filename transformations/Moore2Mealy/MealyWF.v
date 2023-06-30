
Require Import Moore2Mealy.Mealy Moore2Mealy.MealySemantics. 
Import String.
Import Id.

Definition unique_ids (m:M) := 
  forall e1 e2,
  List.In (StateElement e1) m.(Model.modelElements) ->
  List.In (StateElement e2) m.(Model.modelElements) ->
  e1.(State_id) = e2.(State_id) ->
  e1 = e2.

(** Two states with the same id are equals because a state only contains an id. *)
Lemma always_unique_ids :
  forall m, unique_ids m.
  unfold unique_ids.
  intros m e1 e2 H1 H2 E.
  destruct e1, e2.
  simpl in E.
  congruence.
Qed.

(* fixme : generalise-me *)
Lemma In_state : forall (m:Mealy.M) e,
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
    destruct e2 ; [ unfold get_E_data in G ; injection G ; intro ; subst| discriminate G]. 
    assumption.
  }
Qed.

Lemma In_transition : forall (m:Mealy.M) e,
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
    OptionListUtils.find_lift 
      (get_E_data State_K)
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


(** Each node has only one transition getting out of it for a same input. *)
Definition determinist m :=
  forall s t1 t2,
      List.In t1 (State_outTransitions m s) ->
      List.In t2 (State_outTransitions m s) ->
      t1.(Transition_input) = t2.(Transition_input) ->
      t1 = t2.

