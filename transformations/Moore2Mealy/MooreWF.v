
Require Import Moore2Mealy.Moore Moore2Mealy.MooreSemantics.
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
  rewrite OptionListUtils.find_lift_filter_lift.
  match goal with [ |- ?F = _] => destruct F eqn:E ; [ | exfalso ] end.
  + 
    apply List.find_some in E.
    destruct E as (IN2 & EQ).
    apply In_state in IN2.
    f_equal.
    apply H ; [ exact IN2 | exact H0 | ].
    apply internal_NodeId_dec_bl in EQ. 
    congruence.
   + apply List.find_none with (x:= e) in E ; [ |  ].
     rewrite internal_NodeId_dec_lb in E.
     congruence. congruence.
     apply In_state ; assumption.
     
Qed.

(** Each node has only one transition getting out of it for a same input. *)
Definition determinist m := forall s t1 t2,
      List.In t1 (State_outTransitions m s) ->
      List.In t2 (State_outTransitions m s) ->
      t1.(Transition_input) = t2.(Transition_input) ->
      t1 = t2.
