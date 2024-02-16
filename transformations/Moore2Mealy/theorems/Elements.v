From usertools 
       Require TacticsFW TacticsBW.

From transformations.Moore2Mealy 
  Require MooreSemantics MealySemantics MooreWF MealyWF Moore2Mealy.

Import Moore2Mealy OptionUtils Strings.String. (* for notation *)
Open Scope string_scope.

Section Params.

Variable (m:Moore.M).

Hypothesis WF_U : MooreWF.state_id_uniqueness m.
Hypothesis WF_T : Moore.WF_transition_target_exists m.


(** [convert_state] is not injective, but if we consider states of a model with uniqueness of identifiers, it becomes injective. *)

Lemma convert_state_injective : 
  forall s1 s2,
    List.In (Moore.State s1) m.(Model.modelElements) ->
    List.In (Moore.State s2) m.(Model.modelElements) ->
    convert_state s1 = convert_state s2 ->
    s1 = s2.
Proof.
  intros s1 s2 H1 H2 H3.
  apply WF_U ; auto.
  destruct s1, s2 ; unfold convert_state in H3 ; congruence.
Qed.


Lemma convert_transition_injective : 
  forall t1 t2 a, 
    convert_transition m t1 = Some a -> (* would be false with None *)
    convert_transition m t2 = Some a ->
    t1 = t2.
Proof.
  unfold convert_transition ; intros.
  PropUtils.destruct_match_H H ; [ PropUtils.inj H | discriminate H].
  PropUtils.destruct_match_H H0 ; [ PropUtils.inj H0 | discriminate H0].
  
  destruct t1, t2 ; simpl in * ; congruence.
Qed.


Lemma convert_transition_suff : forall t,
    List.In (Moore.Transition t) m.(Model.modelElements) -> 
    SUCCESS (convert_transition m t).
Proof.
  intros t H.
  apply WF_T in H.
  destruct H as [s H].
  unfold convert_transition.
  exists (Mealy.Build_Transition_t t.(Moore.Transition_id) t.(Moore.Transition_input) s.(Moore.State_output)).
  simpl.
  destruct t.
  PropUtils.destruct_match_G.
  + PropUtils.inj H.
    reflexivity.
  + discriminate.
Qed.


Lemma convert_transition_nec :
  forall t t',
  convert_transition m t = Some t' ->
  exists s, 
    Moore.getTransition_target m t = Some s
    /\  t'= {|
              Mealy.Transition_id := Moore.Transition_id t;
              Mealy.Transition_input := Moore.Transition_input t;
              Mealy.Transition_output := Moore.State_output s
            |}.
Proof.
  unfold convert_transition.
  intros  t t' H.
  PropUtils.destruct_match_H H ; [ PropUtils.inj H | discriminate H ].
  eauto.
Qed.


(* FW *)
Lemma state_element_fw  
  (s:Moore.State_t)
  (IN : List.In (Moore.State s) (Model.modelElements m)) :
  List.In 
    (Mealy.State (convert_state s))  
    (Semantics.execute Moore2Mealy m).(Model.modelElements).
Proof. 
  
  (* Simple resolution (not the general case) *)
  Succeed solve [TacticsFW.transform_element_fw_tac].

  (* More general resolution *)
  TacticsFW.in_modelElements_singleton_fw_tac "state" "s" 0 IN ; 
  reflexivity. 
Qed.

Import Semantics Syntax List Model UserExpressions. (* for notations *)

Lemma in_modelElements_inv_m2m :
  forall (sm:Moore.M) e s n lp, 
    In 
      {| 
        TraceLink.source := (s, 0, n);
        TraceLink.produced := e ;
        TraceLink.linkPattern := lp 
      |} 
      (compute_trace Moore2Mealy sm) ->
    In e (execute Moore2Mealy sm).(modelElements) .
Proof.
  setoid_rewrite in_map_iff.
  intros.
  repeat first [eexists | split | eassumption].
  reflexivity.
Qed.

Lemma in_compute_trace_inv_m2m (sm:Moore.M) :
  forall s n res l r opu_el,
      In r Moore2Mealy.(rules) ->
      In {| 
          opu_name := n ;
          opu_element := opu_el ;
          opu_link := l
        |}
        r.(r_outputPattern) ->
       incl s (modelElements sm) ->
       evalGuard r sm s = true ->
       length s = 1 ->
       In 0 (seq 0 (evalIterator r sm s)) ->       
       opu_el 0 sm s = Some res ->
       In 
         {| 
           TraceLink.source := (s, 0, n); 
           TraceLink.produced := res ; 
           TraceLink.linkPattern := l 
         |}
         (compute_trace Moore2Mealy sm). 

Proof. 
  intros.
  apply <- SemanticsTools.in_compute_trace_inv. 
  repeat first [ split | eexists | eauto] ;
  simpl.
  + apply PeanoNat.Nat.eq_le_incl ; auto.
Qed.


Lemma state_element_fw_unfolded  
  (s:Moore.State_t) (sm:Moore.M)
  (IN : In (Moore.State s) sm.(modelElements)) :
  In 
    (Mealy.State (convert_state s))  
    (execute Moore2Mealy sm).(modelElements).
Proof. 
  eapply in_modelElements_inv_m2m.
  eapply in_compute_trace_inv_m2m.
  - (*1*) ChoiceTools.rule_named "state".
  - (*2*) ChoiceTools.pattern_named "s".
  - (*3*) apply ListUtils.incl_singleton; exact IN.
  - (*4*) reflexivity. 
  - (*5*) simpl ; auto. 
  - (*6*) simpl ; auto.
  - (*7*) reflexivity. 
Qed.

(* FW without new tactics *)
Lemma state_element_fw_no_tactic rm s
  (H: rm = Semantics.execute Moore2Mealy m) 
  (IN: List.In (Moore.State s) (Model.modelElements m) ) :
  List.In (Mealy.State (convert_state s))  rm.(Model.modelElements).
Proof.
  subst rm.
  autounfold with semantics.
  rewrite ListUtils.map_flat_map.
  apply List.in_flat_map.
  eexists. (*exists ( (Moore.State s) :: nil ).*)
  split.
  + unfold Semantics.allTuples.
    rewrite  <- TupleUtils.tuples_up_to_n_incl_length. split.
    * apply ListUtils.incl_singleton. exact IN. 
    * simpl. auto.
  + simpl. left. reflexivity.
Qed.


Lemma state_element_bw :
  forall (s:Mealy.State_t),
    List.In (Mealy.State s) (Model.modelElements (Semantics.execute Moore2Mealy m)) ->
    exists s0,
      List.In (Moore.State s0) (Model.modelElements m) /\ s = convert_state s0.
Proof.
  intros s H.
  TacticsBW.exploit_element_in_result H ; eauto.
Qed.


Lemma transition_element_bw :
  forall (t:Mealy.Transition_t),
    List.In (Mealy.Transition t) (Model.modelElements (Semantics.execute  Moore2Mealy.Moore2Mealy m)) ->
    exists t0,
      List.In (Moore.Transition t0) (Model.modelElements m) /\ Some t = convert_transition m t0.
Proof.
  intros t H.
  TacticsBW.exploit_element_in_result H.
  exists t1.
  split ; auto. 
Qed.


(* FW with [in_modelElements_singleton_fw_tac] tactic *)
Lemma transition_element_fw: 
  forall (t:Moore.Transition_t),
    List.In (Moore.Transition t) (Model.modelElements m) ->
    exists t', 
      convert_transition m t = Some t' /\
        List.In (Mealy.Transition t')  (Semantics.execute  Moore2Mealy.Moore2Mealy m).(Model.modelElements).
Proof.
  intros t IN.
  destruct (WF_T _ IN) as (s & G).

  assert ( C : convert_transition m t = Some
             {|
               Mealy.Transition_id := Moore.Transition_id t;
               Mealy.Transition_input := Moore.Transition_input t;
               Mealy.Transition_output := Moore.State_output s
             |}).
  { unfold convert_transition. rewrite G. reflexivity. }

  rewrite C.
  eexists ; split ; [ reflexivity| ].


  TacticsFW.in_modelElements_singleton_fw_tac "transition" "t" 0 IN ;
  try reflexivity ; [].
  (* Here we would like to "compute", but this does not work because the value of this computation relies on the value of [m], which is unknown here ; we have to [rewrite C] to get rid of the value of [m]. *)
  simpl.

    unfold ConcreteExpressions.makeElement ; simpl.
    unfold ConcreteExpressions.wrapElement ; simpl.
    rewrite C. reflexivity.
Qed.

(* FW with [transform_element_fw_tac] tactic *)
Lemma transition_element_fw_alt : 
  forall (t:Moore.Transition_t),
    List.In (Moore.Transition t) (Model.modelElements m) ->
    exists t', 
      convert_transition m t = Some t' /\
        List.In (Mealy.Transition t')  (Semantics.execute  Moore2Mealy.Moore2Mealy m).(Model.modelElements).
Proof.
  intros t IN.
  destruct (WF_T _ IN) as (s & G).

  assert ( C : convert_transition m t = Some
             {|
               Mealy.Transition_id := Moore.Transition_id t;
               Mealy.Transition_input := Moore.Transition_input t;
               Mealy.Transition_output := Moore.State_output s
             |}).
  { unfold convert_transition. rewrite G. reflexivity. }

  rewrite C.
  eexists ; split ; [ reflexivity| ].
  TacticsFW.transform_element_fw_tac ; [].
  (* Here we would like to "compute", but this does not work because the value of this computation relies on the value of [m], which is unknown here ; we have to [rewrite G] to get rid of the value of [m]. *)
  simpl.
  
  autounfold with parse.
  autounfold with trace.
  
  apply List.in_map_iff.
  setoid_rewrite List.in_flat_map.
  eexists ; split ; [ | eexists ; split ; [ ChoiceTools.first_in_list | ]].


  2:{
    autounfold with parse ; simpl.

    unfold ConcreteExpressions.makeElement ; simpl.
    unfold ConcreteExpressions.wrapElement ; simpl.
    rewrite C. left ; reflexivity.
  }
  { reflexivity. }
Qed.


End Params.
