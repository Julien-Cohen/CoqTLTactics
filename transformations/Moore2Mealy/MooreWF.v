
Require Import Moore MooreSemantics. 
Import String.

Definition unique_names (m:MooreModel) := 
  forall e1 e2,
  List.In (StateElement e1) m.(Model.modelElements) ->
  List.In (StateElement e2) m.(Model.modelElements) ->
  e1.(name) = e2.(name) ->
  e1 = e2.


Lemma in_find : 
  forall m n e,
    unique_names m ->
    List.In e (MooreMetamodel_allStates m) ->
    e.(name) = n ->
    List.find
           (fun s : State => (n =? s.(name))%string)
           (MooreMetamodel_allStates m) = 
         Some e.
Proof.
  intros.
  match goal with [ |- ?F = _] => destruct F eqn:E ; [ | exfalso ] end.
  + apply List.find_some in E.
    destruct E as (IN2 & EQ).
    f_equal.
    apply H.
    * unfold MooreMetamodel_allStates in IN2.
      unfold MooreMetamodel_toStates in IN2.
      apply ListUtils.optionList2List_In in IN2.
      apply List.in_map_iff in IN2.
      destruct IN2 as (a & T & IN2).
      unfold get_E_Data in T.
      destruct a. 
      - PropUtils.inj T.
        exact IN2.
      - discriminate T.
    * (* same as above *)
      unfold MooreMetamodel_allStates in H0.
      unfold MooreMetamodel_toStates in H0.
      apply ListUtils.optionList2List_In in H0.
      apply List.in_map_iff in H0.
      destruct H0 as (a & T & H0).
      unfold get_E_Data in T.
      destruct a. 
      - PropUtils.inj T.
        exact H0.
      - discriminate T.
        * apply String.eqb_eq in EQ.
          congruence.
   + apply List.find_none with (x:=e) in E ; [ | assumption ].
     apply String.eqb_neq in E.
     congruence.
Qed.
