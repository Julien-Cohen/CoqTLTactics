
Require Import Mealy MealySemantics. 
Import String.

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

Lemma in_find : 
  forall m n e,
    unique_names m ->
    List.In e (MealyMetamodel_allStates m) ->
    e.(State_name) = n ->
    List.find
           (fun s : State_t => (n =? s.(State_name))%string)
           (MealyMetamodel_allStates m) = 
         Some e.
Proof.
  intros.
  destruct e ; simpl in * ; subst.
  match goal with [ |- ?F = _] => destruct F eqn:E ; [ | exfalso ] end.
  + f_equal. 
    apply List.find_some in E.
    destruct E as (IN2 & EQ).
    destruct s.
    f_equal.
    apply String.eqb_eq in EQ. subst ; reflexivity. 
   + apply List.find_none with (x:={| State_name := n |}) in E ; [ | assumption ].
     apply String.eqb_neq in E.
     simpl in E.
     contradiction.
Qed.
