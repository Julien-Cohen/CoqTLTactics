
Require Import Moore2MealyALT.Mealy Moore2MealyALT.MealySemantics. 
Import String.
Import Id.

Definition unique_names (m:M) := 
  forall e1 e2,
  List.In (StateElement e1) m.(Model.modelElements) ->
  List.In (StateElement e2) m.(Model.modelElements) ->
  e1.(State_name) = e2.(State_name) ->
  e1 = e2.

(** Two states with the same name are equals because a state only contains a name. *)
Lemma always_unique_names :
  forall m, unique_names m.
  unfold unique_names.
  intros m e1 e2 H1 H2 E.
  destruct e1, e2.
  simpl in E.
  congruence.
Qed.

(* fixme : generalise-me *)
Lemma In_1 : forall (m:Mealy.M) e,
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

Lemma in_find : (* fixme : use the concept of discriminant proposition for the proof *)
  forall m n e,
    unique_names m ->
    List.In (StateElement e) m.(Model.modelElements) ->
    e.(State_name) = n ->
    OptionListUtils.find_lift 
      (get_E_data State_K)
      (fun s : State_t => (NodeId_beq n s.(State_name))%string)
           m.(Model.modelElements) = 
         Some e.
Proof.
  intros.
  rewrite OptionListUtils.find_lift_filter_lift.
  destruct e ; simpl in * ; subst.
  match goal with [ |- ?F = _] => destruct F eqn:E ; [ | exfalso ] end.
  + f_equal. 
    apply List.find_some in E.
    destruct E as (IN2 & EQ).
    apply In_1 in IN2.
    apply internal_NodeId_dec_bl in EQ. subst. apply H ; auto.
  + apply List.find_none with (x:= {| State_name := n |}) in E ; [ |  ].
    simpl in E.
    rewrite internal_NodeId_dec_lb in E. discriminate. reflexivity.
     apply In_1.  assumption.
Qed.


(** Each node has only one transition getting out of it for a same input. *)
Definition determinist m :=
  forall s t1 t2,
      List.In t1 (State_outTransitions m s) ->
      List.In t2 (State_outTransitions m s) ->
      t1.(Transition_input) = t2.(Transition_input) ->
      t1 = t2.
