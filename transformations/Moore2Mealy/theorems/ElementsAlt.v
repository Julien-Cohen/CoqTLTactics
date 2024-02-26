From usertools 
       Require TacticsFW.

From transformations.Moore2Mealy 
  Require MooreSemantics MealySemantics MooreWF MealyWF Moore2Mealy.

Import Moore2Mealy OptionUtils Strings.String. (* for notation *)
Open Scope string_scope.

(** This file contains alternative proofs for a lemma available in the module Elements, used for didactic developments. *)


(** Alternative 1 : general sheme for proving FW results on elements, without tactics. *)


Import Semantics Syntax List Model UserExpressions. (* for notations *)

(* Two local lemmas *)
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

(** A result that uses those lemmas. *)
Theorem state_element_fw_unfolded  
  (sm:Moore.M) (s:Moore.State_t) 
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



(** Alternative 2 : general scheme for proving FW results on elements, with a tactic (a single tactic is given, which is equivalent to inlining several tactics given in TacticsFW). *)


(* Inlined version of TacticsFW.in_modelElements_singleton_fw_tac *)
Ltac in_modelElements_singleton_fw_tac r_name pat_name i H
  :=
  match type of H with
  | List.In _ ?M.(modelElements) =>
      match goal with
      | |- List.In _ (execute ?T M).(modelElements)
        => idtac
      end
  end; 
  apply <- SemanticsTools.in_modelElements_inv; 
  eexists; exists i; eexists; eexists;
  
  eapply SemanticsTools.in_compute_trace_inv_left ;
  
  (* 7 goals *)
  [ | | | | | | ] ;
  
  
  [ (* Fix the rule under concern following user hint *)
    solve [ChoiceTools.rule_named r_name] 
          
  | (* Fix the output pattern in the rule following user hint *)
    solve [ChoiceTools.pattern_named pat_name] 
          
  | (* Fix the source piece *)
    ListUtils.solve_incl_singleton H
                                   
  | (* The guard goal may rely on user expressions and can be arbitrary difficult to prove *)
    simpl
      
  | (* arity *) 
    solve [simpl ; auto] 
          
  | (* iteration counter *)
    solve [simpl ; auto ] 
          
  | (* The make_element goal relies on user expressions and can be arbitrary difficult to prove *) 
    simpl 
      
  ] .

Theorem state_element_fw_alt  
  (sm:Moore.M) (s:Moore.State_t)
  (IN : List.In (Moore.State s) sm.(modelElements)) :
  List.In 
    (Mealy.State (convert_state s))  
    (execute Moore2Mealy sm).(modelElements).
Proof. 
  
  in_modelElements_singleton_fw_tac "state" "s" 0 IN ; 
  reflexivity. 
Qed.


(** Alternative for [transition_element_fw] *)

(* FW with [transform_element_fw_tac] tactic *)
Lemma transition_element_fw_alt : 
  forall  (m:Moore.M) (t:Moore.Transition_t),
    Moore.WF_transition_target_exists m ->
    List.In (Moore.Transition t) (Model.modelElements m) ->
    exists t', 
      convert_transition m t = Some t' /\
        List.In (Mealy.Transition t')  (Semantics.execute  Moore2Mealy.Moore2Mealy m).(Model.modelElements).
Proof.
  intros m t WF_T IN.
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
