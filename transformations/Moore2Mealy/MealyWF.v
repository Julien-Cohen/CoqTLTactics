
Require Import Mealy MealySemantics. 
Import String.

Definition unique_names (m:MealyModel) := 
  forall e1 e2,
  List.In (Build_MealyMetamodel_Object State_K e1) m.(Model.modelElements) ->
  List.In (Build_MealyMetamodel_Object State_K e2) m.(Model.modelElements) ->
  e1.(name) = e2.(name) ->
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
    e.(name) = n ->
    List.find
           (fun s : State => (n =? s.(name))%string)
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
   + apply List.find_none with (x:={| name := n |}) in E ; [ | assumption ].
     apply String.eqb_neq in E.
     simpl in E.
     contradiction.
Qed.
