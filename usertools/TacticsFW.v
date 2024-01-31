Require Import core.Semantics.

Import 
  Metamodel Model NotationUtils List core.TransformationConfiguration.

From usertools 
  Require SemanticsTools ChoiceTools Backtracking.

(** * FW Tactics on traces *)

(** ** Tactics that fully unfold [In _ compute_trace _ _] and solve easy goals. *) 

(** This version, for rules with singleton patterns, takes as parameter the index of the rule and the index of the output pattern in that rule. *)
Ltac in_compute_trace_inv_singleton_fw r_num pat_num :=
  match goal with 
  | [ |- List.In _ (compute_trace ?T _)] => 
     
      SemanticsTools.in_compute_trace_inv_tac ;

      (* 7 goals *)
      [ | | | | | | ] ;
      
      (* Begin with goals that do not need backtracking. *)
      
      (* Fix the rule under concern following user hint *)
      only 3 : solve [ChoiceTools.rule_number r_num] (* no backtrack needed *) ;

      (* Fix the output pattern in the rule following user hint *)
      only 5 : solve [ChoiceTools.pattern_number pat_num] ;

      (* Fix the source piece using the context (singleton version) *)
      only 1 : 
        (apply ListUtils.incl_singleton ;
         Backtracking.multi_eassumption (* backtrack point *)) ; 


      (* Check that the instantiation made at the previous step is type-safe, otherwise backtrack. *)
      only 2 : (* guard *) Backtracking.fail_on_type_mismatch ; 

      (* Solve remaining simple goals : arity and iteration-counter *)
      only 1 : reflexivity ; 
      only 2 : solve [simpl ; auto (* left ; reflexivity *) ] ;

      (* The two remaining goals rely on user expressions and can be arbitrary difficult to prove *)
      only 1 : (* guard *) simpl ;
      only 2 : (* make_element *) simpl ;
      try reflexivity (* solve "simple" evalGuard & make_element goals *)
  end. (* problem : does not always choose the correct assumption *)

(* The choice of the correct assumption is an additional choice, after the choice of the correct rule and of the correct out-patter of the rule (and the choice of the iteration counter). Can we set this choice as a parameter of the tactic, and after that add a tactic that searches for the correct parameter ? *)


(* Tactic with reordered subgoals so that the numbering is not necessary. *)
Ltac in_compute_trace_inv_singleton_fw_solve_reordered r_num pat_num :=
  match goal with 
  | [ |- List.In _ (compute_trace ?T _)] => 
     
      SemanticsTools.in_compute_trace_inv_tac_reordered ;

      (* 7 goals *)
      [ | | | | | | ]  ;
      
      (* Begin with goals that do not need backtracking. *)
      
      (* Fix the rule under concern following user hint *)
      [ solve [ChoiceTools.rule_number r_num] (* no backtrack needed *) 

      (* Fix the output pattern in the rule following user hint *)
      | solve [ChoiceTools.pattern_number pat_num] 

      (* Fix the source piece using the context (singleton version) *)
      | apply ListUtils.incl_singleton ;
         Backtracking.multi_eassumption (* backtrack point *) 


      (* Check that the instantiation made at the previous step is type-safe, otherwise backtrack. *)
      | (* guard *) reflexivity 
      

      | reflexivity (* arity *)  
      | solve [simpl ; auto ] (* iteration-counter *) 
        
      | reflexivity (* make_element *)
] 
  end. 



Ltac in_compute_trace_inv_singleton_fw_solve r_num pat_num :=
  match goal with 
  | [ |- List.In _ (compute_trace ?T _)] => 
     
      SemanticsTools.in_compute_trace_inv_tac ;

      (* 7 goals *)
      [ | | | | | | ] ;
      
      (* Begin with goals that do not need backtracking. *)
      
      (* Fix the rule under concern following user hint *)
      only 3 : solve [ChoiceTools.rule_number r_num] (* no backtrack needed *) ;

      (* Fix the output pattern in the rule following user hint *)
      only 5 : solve [ChoiceTools.pattern_number pat_num] ;

      (* Fix the source piece using the context (singleton version) *)
      only 1 : 
        ( apply ListUtils.incl_singleton ;
          Backtracking.multi_eassumption (* backtrack point *) ) ; 

      (* FIXME : set a unit test that need backtracking here. *)

      (* Check that the instantiation made at the previous step is type-safe, otherwise backtrack. *)
      only 2 : (* guard *) Backtracking.fail_on_type_mismatch ; 

      (* Solve remaining simple goals : arity and iteration-counter *)
      only 1 : reflexivity ; 
      only 2 : solve [simpl ; auto] ;

      (* The two remaining goals rely on user expressions and can be arbitrary difficult to prove *)
      only 1 : (* guard *) simpl ;
      only 2 : (* make_element *) simpl ;
      reflexivity (* solve evalGuard & make_element goals *)
  end.

(** Variant for pair patterns *)
Ltac in_compute_trace_inv_pair_fw r_num pat_num :=
  match goal with 
  | [ |- List.In _ (compute_trace ?T _)] => 
      
      SemanticsTools.in_compute_trace_inv_tac ;

      (* 7 goals *)
      [ | | | | | | ] ;
      
      (* Begin with goals that do not need backtracking. *)
      
      (* Fix the rule under concern following user hint *)
      only 3 : solve [ChoiceTools.rule_number r_num] ;
      
      (* Fix the output pattern in the rule following user hint *)
      only 5 : solve [ChoiceTools.pattern_number pat_num] ;
      
      (* Fix the source piece using the context (pair version) *)
      only 1 : 
        ( apply ListUtils.incl_pair ; split ;
          Backtracking.multi_eassumption (* two backtrack points *) ) ;

      
      (* Check that the instantiation made at the previous step is type-safe, otherwise backtrack. *)
      only 2 : Backtracking.fail_on_type_mismatch ;
      
      (* Solve remaining simple goals : arity and iteration-counter *)
      only 1 : reflexivity ;
      only 2 : solve [compute ; auto] ;
      
      (* The two remaining goals rely on user expressions and can be arbitrary difficult to prove *)
      only 1 : simpl ;
      only 2 : simpl ;
      try reflexivity
  end.


(** Variant that tries to guess the rule and the pattern *)
Ltac in_compute_trace_inv_singleton_fw_auto := 
  SemanticsTools.in_compute_trace_inv_tac ;

  (* 7 goals *)
  [ | | | | | | ] ;
  
  (* Fix the rule under concern (try and backtrack) *)
  only 3: (ChoiceTools.first_rule + ChoiceTools.second_rule) ;
  
  (* Fix the output pattern in the rule (try and backtrack) *)
  only 5 : (ChoiceTools.first_in_list + ChoiceTools.second_in_list) ;
  
  (* Fix the source piece using the context (singleton version) *)
  only 1 : 
    ( apply ListUtils.incl_singleton ;
      Backtracking.multi_eassumption (* backtrack point *) ); 
 
  (* Check that the instantiation made at the previous step is type-safe, otherwise backtrack. *)
  only 2 : Backtracking.fail_on_type_mismatch ;

  (* Solve remaining simple goals : arity and iteration-counter *)
  only 1 : reflexivity ;
  only 2 : solve [simpl; auto] ;  

  (* The two remaining goals rely on user expressions and can be arbitrary difficult to prove *)
  only 1 : simpl ;
  only 2 : simpl ;
  try reflexivity.








(** * FW tactics on Elements and Links *)

(** *** On elements (singletons, then pairs) *)

Ltac in_modelElements_singleton_fw_tac r_num pat_num i :=
  match goal with 
    [ |- List.In _  (execute ?T _).(modelElements) ] =>

      apply <- SemanticsTools.in_modelElements_inv ; 

      eexists ; exists i ; eexists ; eexists ; 

      in_compute_trace_inv_singleton_fw r_num pat_num ;

      try reflexivity
  end.


Ltac in_modelElements_pair_fw_tac r_num pat_num i:=
  match goal with 
    [ |- In _  (execute _ _).(modelElements) ] =>

      apply <- SemanticsTools.in_modelElements_inv ; 

      eexists ; exists i ; eexists ; eexists ; 

      in_compute_trace_inv_pair_fw r_num pat_num ;

      try reflexivity 
  end.

(** *** On links (singleton), two versions *)

Ltac transform_link_fw_tac_singleton r_num pat_num i :=
  match goal with
    [ |- In _ (execute _ _).(modelLinks) ] =>

      apply <- SemanticsTools.in_modelLinks_inv ; 
      
      eexists ; exists i ; eexists ; eexists ; eexists ; 

      split ; 
      
      [ in_compute_trace_inv_singleton_fw r_num pat_num | ] ;
      
      autounfold with 
        parse ConcreteOutputPatternUnit_accessors opu_accessors 
  end.

(** Variant where the first rule that don't lead to an error is selected instead of relying on an user hint. *)
Ltac transform_link_fw_tac_singleton_auto i :=
  match goal with
    [ |- In _ (execute _ _).(modelLinks) ] =>

      apply <- SemanticsTools.in_modelLinks_inv ; 

      eexists ; exists i ; eexists ; eexists ; eexists ; 
      
      split ;

      [ in_compute_trace_inv_singleton_fw_auto | ] ;
  
      (* Fail if one of the goal reduces to False 
         (trigger backtracking)                   *)
      Backtracking.fail_on_False ;   
  
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

