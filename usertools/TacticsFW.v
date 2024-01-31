Require Import core.Semantics.

Import 
  Metamodel Model NotationUtils List core.TransformationConfiguration.

From usertools 
  Require SemanticsTools ChoiceTools (*Backtracking*).

(** * FW Tactics on traces *)

(** ** Tactics that fully unfold [In _ compute_trace _ _] and solve easy goals. *) 

(** This version, for rules with singleton patterns, takes as parameter the index of the rule, the index of the output pattern in that rule, and the source element hypothesis. *)
Ltac in_compute_trace_inv_singleton_fw r_num pat_num H :=
  match goal with 
  | [ |- List.In _ (compute_trace ?T _)] => 
     
      SemanticsTools.in_compute_trace_inv_tac ;

      (* 7 goals *)
      [ | | | | | | ] ;
      

      [ (* Fix the rule under concern following user hint *)
        solve [ChoiceTools.rule_number r_num] 
              
      | (* Fix the output pattern in the rule following user hint *)
        solve [ChoiceTools.pattern_number pat_num] 
              
      | (* Fix the source piece (singleton) *)
        apply ListUtils.incl_singleton ; exact H 

      | (* The guard goal may rely on user expressions and can be arbitrary difficult to prove *)
        simpl

      | (* arity *) 
        reflexivity 

      | (* iteration counter *)
        solve [simpl ; auto ] 

      

      | (* The make_element goal rely on user expressions and can be arbitrary difficult to prove *) 
        simpl 
      ] ;

      try reflexivity (* solve "simple" evalGuard & make_element goals *)
  end. 




(** Variant for pair patterns *)
Ltac in_compute_trace_inv_pair_fw r_num pat_num H1 H2 :=
  match goal with 
  | [ |- List.In _ (compute_trace ?T _)] => 
      
      SemanticsTools.in_compute_trace_inv_tac ;

      (* 7 goals *)
      [ | | | | | | ] ;

      [ (* Fix the rule under concern following user hint *)
        solve [ChoiceTools.rule_number r_num] 
      
      | (* Fix the output pattern in the rule following user hint *) 
        solve [ChoiceTools.pattern_number pat_num] 

      | (* Fix the source piece (pair) *) 
        apply ListUtils.incl_pair ; split ; [ exact H1 | exact H2 ] 
      
      | (* The guard goal may rely on user expressions and can be arbitrary difficult to prove *)  
        simpl

      | (* arity *)
        reflexivity 
      
      | (* iteration counter *)
        solve [simpl ; auto ] 

      | (* The make_element goal rely on user expressions and can be arbitrary difficult to prove *)      
        simpl 
      ] ;
      
      try reflexivity (* solve "simple" evalGuard & make_element goals *)

  end.





(** * FW tactics on Elements and Links *)

(** *** On elements (singletons, then pairs) *)

Ltac in_modelElements_singleton_fw_tac r_num pat_num i H :=
  match goal with 
    [ |- List.In _ (execute ?T _).(modelElements) ] =>

      apply <- SemanticsTools.in_modelElements_inv ; 

      eexists ; exists i ; eexists ; eexists ; 

      in_compute_trace_inv_singleton_fw r_num pat_num H ;

      try reflexivity
  end.


Ltac in_modelElements_pair_fw_tac r_num pat_num i H1 H2 :=
  match goal with 
    [ |- In _ (execute _ _).(modelElements) ] =>

      apply <- SemanticsTools.in_modelElements_inv ; 

      eexists ; exists i ; eexists ; eexists ; 

      in_compute_trace_inv_pair_fw r_num pat_num H1 H2 ;

      try reflexivity 
  end.

(** *** On links (singleton), two versions *)

Ltac transform_link_fw_tac_singleton r_num pat_num i H :=
  match goal with
    [ |- In _ (execute _ _).(modelLinks) ] =>

      apply <- SemanticsTools.in_modelLinks_inv ; 
      
      eexists ; exists i ; eexists ; eexists ; eexists ; 

      split ; 
      
      [ in_compute_trace_inv_singleton_fw r_num pat_num H | ] ;
      
      autounfold with 
        parse ConcreteOutputPatternUnit_accessors opu_accessors 
  end.


(** * Simple tactics (for simple situations) *)

(** A simple FW tactic for elements (lemma + tactic) (only
    singleton patterns).  The drawback of this lemma/tactic
    is that when the traceTrOnPiece premise is not solved by
    auto, it leaves the user with a painful subgoal. *)
Lemma transform_element_fw {tc} (t:Syntax.Transformation (tc:=tc)) cm e te  :
  0 < Syntax.arity t ->
  In e cm.(modelElements) ->
  In te (produced_elements (traceTrOnPiece t cm [e])) ->
  In te (execute t cm).(modelElements).
Proof.
  intros A IN1 IN2.
  simpl.
  unfold compute_trace, produced_elements.
  rewrite ListUtils.map_flat_map. (* a trace can have several target elements *)
  apply List.in_flat_map. (* this is doing the job *)
  exists ([e]) ; split ; [ | auto ].
  apply <- SemanticsTools.in_allTuples_singleton. auto.
Qed.

Ltac transform_element_fw_tac :=
  match goal with
    [ |- In _ (execute ?T _).(modelElements) ] =>
      eapply (transform_element_fw T) ; 
      [ solve [ simpl ; auto ] 
      | (*try*) eassumption 
      | try (solve [simpl;auto])]
  end.

