
Require Import Moore2Mealy.Mealy Moore2Mealy.MealySemantics. 
Import String.
Import Id Glue.

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


(** Two different (source) links cannot deal with the same transition. *)
(** A transition starts at only one state. *)
Definition WF_sourceLink_left (m:Mealy.M) : Prop :=
      forall (lk1 lk2 : Transition_source_t) (t : Transition_t),
        List.In (Transition_sourceLink lk1)  m.(Model.modelLinks) ->
        List.In (Transition_sourceLink lk2)  m.(Model.modelLinks) ->
        lk1.(lglue) = t ->
        lk2.(lglue) = t ->
        lk1 = lk2.

(** Two different (target) links cannot deal with the same transition. *)
(** A transition aims at only one state. *)
Definition WF_targetLink_left (m:Mealy.M) : Prop :=
      forall (lk1 lk2 : Transition_target_t) (t : Transition_t),
        List.In (Transition_targetLink lk1)  m.(Model.modelLinks) ->
        List.In (Transition_targetLink lk2)  m.(Model.modelLinks) ->
        lk1.(lglue) = t ->
        lk2.(lglue) = t ->
        lk1 = lk2.
  

Lemma getTransition_source_some (m:Mealy.M):
  WF_sourceLink_left m ->
  forall s,
    List.In (StateElement s) m.(Model.modelElements) ->
    forall t,
      let lk := {| lglue := t ; rglue := s |} 
      in
      
      List.In (Transition_sourceLink lk) (Model.modelLinks m) ->

      getTransition_source m t = Some s. 
Proof.
  intros WF s H1 t lk H2.
  unfold getTransition_source.
  unfold getTransition_sourceOnLinks.
  apply OptionUtils.option_map_some with (b:=lk).
  2:{ subst lk ; reflexivity. }
  subst lk.
  eapply OptionListUtils.in_find_lift.

  {
    intro ; intros.
    apply internal_Transition_t_dec_bl in H3.
    apply internal_Transition_t_dec_bl in H4.
    eapply WF ; eauto.
    apply In_transition_sourceLink ; assumption.
    apply In_transition_sourceLink ; assumption.
  }    
  { 
    instantiate (1:=Transition_sourceLink {| lglue := t; rglue := s |}). 
    reflexivity.
  }        

  { apply internal_Transition_t_dec_lb. reflexivity. }
  { assumption. }
Qed.

Lemma getTransition_target_some (m:Mealy.M):
  WF_targetLink_left m ->
  forall s,
    List.In (StateElement s) m.(Model.modelElements) ->
    forall t,
      let lk := {| lglue := t ; rglue := s |} 
      in
      
      List.In (Transition_targetLink lk) (Model.modelLinks m) ->

      getTransition_target m t = Some s. 
Proof.
  intros WF s H1 t lk H2.
  unfold getTransition_target.
  unfold getTransition_targetOnLinks.
  apply OptionUtils.option_map_some with (b:=lk).
  2:{ subst lk ; reflexivity. }
  subst lk.
  eapply OptionListUtils.in_find_lift.

  {
    intro ; intros.
    apply internal_Transition_t_dec_bl in H3.
    apply internal_Transition_t_dec_bl in H4.
    eapply WF ; eauto.
    apply In_transition_targetLink ; assumption.
    apply In_transition_targetLink ; assumption.
  }    
  { instantiate (1:=Transition_targetLink {| lglue := t; rglue := s |}). 
    reflexivity.
  }        

  { apply internal_Transition_t_dec_lb. reflexivity. }
  { assumption. }
Qed.
  


(** Each node has only one transition getting out of it for a same input. *)
Definition determinist m :=
  forall s t1 t2,
      List.In t1 (State_outTransitions m s) ->
      List.In t2 (State_outTransitions m s) ->
      t1.(Transition_input) = t2.(Transition_input) ->
      t1 = t2.


Lemma truc m :
  determinist m ->
  MealySemantics.WF_sourceLink_source_in m ->
  forall s i,
    ListUtils.discriminating_predicate
      (fun x : Transition_t =>
         (i =? Transition_input x)%string = true)
      (MealySemantics.State_outTransitions m s).
Proof.
  intros WF WF2.
  intros s i.
  intros t1 t2 H1 H2 P1 P2.
  unfold State_outTransitions in H1, H2.
  apply OptionListUtils.filter_lift_in in H1, H2.
  destruct H1 as ( ? & ? & ? & ?).
  destruct H2 as ( ? & ? & ? & ?).
  PropUtils.destruct_match H1 ; [ | discriminate H1].
  PropUtils.destruct_match H4 ; [ | discriminate H4].
  destruct x ; [ discriminate H0 | PropUtils.inj H0]. (* monadInv *)
  destruct x0 ; [ discriminate H3 | PropUtils.inj H3]. (* monadInv *)
  apply internal_State_t_dec_bl in H1, H4.
  subst s1 s0.
    apply String.eqb_eq in P1.
    apply String.eqb_eq in P2.
    
  eapply WF ; auto ; [ | | ].
  { apply in_State_outTransitions ; eauto.  }
  {  apply in_State_outTransitions ; eauto. }
  
  { congruence. }
Qed.


Lemma State_acceptTransition_some :
  forall m s i r,
    determinist m ->
    MealySemantics.WF_sourceLink_source_in m ->
    r.(Transition_input) = i ->
    List.In r (State_outTransitions m s) ->
    State_acceptTransition m s i = Some r.
Proof.
  intros.
  unfold State_acceptTransition.
  apply ListUtils.in_find.
  { apply truc ; assumption. }
  { apply String.eqb_eq. auto. }
  { assumption. }
Qed.

