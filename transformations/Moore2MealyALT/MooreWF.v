
Require Import Moore2MealyALT.Moore Moore2MealyALT.MooreSemantics. 
Import String.
Import Id.

Definition unique_names (m:Moore.M) := 
  forall e1 e2,
    List.In (StateElement e1) m.(Model.modelElements) ->
    List.In (StateElement e2) m.(Model.modelElements) ->
    e1.(State_name) = e2.(State_name) ->
    e1 = e2.

Lemma In_1 : forall (m:Moore.M) e,
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

Lemma in_find : 
  forall m n e,
    unique_names m ->
    List.In (StateElement e) m.(Model.modelElements) ->
    e.(State_name) = n ->
    OptionListUtils.find_lift (get_E_data State_K)
           (fun s : State_t => (NodeId_beq n  s.(State_name))%string)
           m.(Model.modelElements) = 
         Some e.
Proof.
  intros.
  rewrite OptionListUtils.find_lift_filter_lift.
  match goal with [ |- ?F = _] => destruct F eqn:E ; [ | exfalso ] end.
  + 
    apply List.find_some in E.
    destruct E as (IN2 & EQ).
    apply In_1 in IN2.
    f_equal.
    apply H ; [ exact IN2 | exact H0 | ].
    apply internal_NodeId_dec_bl in EQ.
    congruence.
   + apply List.find_none with (x:= e) in E ; [ |  ].
     subst.
     rewrite internal_NodeId_dec_lb in E ; auto. discriminate E.

     apply In_1 ; assumption.
     
Qed.

(** Each node has only one transition getting out of it for a same input. *)
Definition determinist (m:Moore.M) := 
  forall t1 t2,
      List.In (TransitionElement t1) m.(Model.modelElements)->
      List.In (TransitionElement t2) m.(Model.modelElements)->
      t1.(Transition_source) = t2.(Transition_source) ->
      t1.(Transition_input) = t2.(Transition_input) ->
      t1 = t2.
