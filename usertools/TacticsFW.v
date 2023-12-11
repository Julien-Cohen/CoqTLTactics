Require Import core.Semantics.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Require SemanticsTools.

Import Metamodel Model.


Require usertools.TacticUtils.

(** * FW Tactics on traces *)

(** ** Tactics that fully unfold [In _ compute_trace _ _] and solve easy goals. *) 

 Ltac in_compute_trace_inv_singleton_fw r_num pat_num :=
  match goal with 
  | [ |- List.In _ (Semantics.compute_trace ?T _)] => 
      apply <- SemanticsTools.in_compute_trace_inv ; 
      split ; 
      [ | split ;
          [ | eexists ; split ; 
              [ | split ; 
                  [ | split ;
                      [ | eexists ; split 
                          ; [ | ]]]]]] ; 
      
      (* Begin with goals that do not need backtracking. *)
      
      (* Fix the rule under concern following user hint *)
      only 3 : solve [TacticUtils.rule_number r_num] (* no backtrack needed *) ;

      (* Fix the output pattern in the rule following user hint *)
      only 5 : solve [TacticUtils.pattern_number pat_num] ;

      (* Fix the source piece using the context (singleton version) *)
      only 1 : apply ListUtils.incl_singleton ;
      only 1 : TacticUtils.multi_eassumption (* backtrack point *); 

      (* Check that the instantiation made at the previous step is type-safe, otherwise backtrack. *)
      only 2 : (* guard *) TacticUtils.fail_on_type_mismatch ; 

      (* Solve remaining simple goals : arity and iteration-counter *)
      only 1 : solve [simpl ; auto] ; 
      only 2 : solve [simpl ; auto] ;

      (* The two remaining goal rely on user expressions and can be arbitrary difficult to prove *)
      only 1 : (* guard *) simpl ;
      only 2 : (* make_element *) simpl ;
      try reflexivity (* solve "simple" evalGuard & make_element goals *)
  end.

(* Variant for pair patterns *)
Ltac in_compute_trace_inv_pair_fw r_num pat_num :=
  match goal with 
  | [ |- List.In _ (Semantics.compute_trace ?T _)] => 
      apply <- SemanticsTools.in_compute_trace_inv ; 
      split ; 
      [ | split ; 
          [ | eexists ; split ; 
              [ | split ; 
                  [ | split ; 
                      [ | eexists ; split ; 
                          [ | ]]]]]] ;
      
      (* Begin with goals that do not need backtracking. *)
      
      (* Fix the rule under concern following user hint *)
      only 3 : solve [TacticUtils.rule_number r_num] ;
      
      (* Fix the output pattern in the rule following user hint *)
      only 5 : solve [TacticUtils.pattern_number pat_num] ;
      
      (* Fix the source piece using the context (pair version) *)
      only 1 : (apply ListUtils.incl_pair ; split)  ;
      only 1 : TacticUtils.multi_eassumption (* backtrack point *);
      only 1 : TacticUtils.multi_eassumption (* backtrack point *); 
      
      (* Check that the instantiation made at the previous step is type-safe, otherwise backtrack. *)
      only 2 : TacticUtils.fail_on_type_mismatch ;
      
      (* Solve remaining simple goals : arity and iteration-counter *)
      only 1 : solve [compute ; auto] ;
      only 2 : solve [compute ; auto] ;
      
      (* The two remaining goal rely on user expressions and can be arbitrary difficult to prove *)
      only 1 : simpl ;
      only 2 : simpl ;
      try reflexivity
  end.


(* Variant that tries to guess the rule and the pattern *)
Ltac in_compute_trace_inv_singleton_fw_auto := 
  apply <- SemanticsTools.in_compute_trace_inv ;
  split ; 
  [ (*1*) | split ; 
    [ (* 2 *) |  eexists ; split ; 
       [ (* 3 *) | split ;
         [(* 4 *) | split ;
           [ (* 5 *) |  eexists ; split ; 
              [ (*6*) | (*7*)] ]]] ] ] ;
  
  
  (* Fix the rule under concern (try and backtrack) *)
  only 3: (TacticUtils.first_rule + TacticUtils.second_rule) ;
  
  (* Fix the output pattern in the rule (try and backtrack) *)
  only 5 : (TacticUtils.first_in_list + TacticUtils.second_in_list) ;
  
  (* Fix the source piece using the context (singleton version) *)
  only 1 : apply ListUtils.incl_singleton ;
  only 1 : TacticUtils.multi_eassumption (* backtrack point *); 
 
  (* Check that the instantiation made at the previous step is type-safe, otherwise backtrack. *)
  only 2 : TacticUtils.fail_on_type_mismatch ;

  (* Solve remaining simple goals : arity and iteration-counter *)
  only 1 : solve [simpl; auto] ;
  only 2 : solve [simpl; auto] ;  

  (* The two remaining goal rely on user expressions and can be arbitrary difficult to prove *)
  only 1 : simpl ;
  only 2 : simpl ;
  try reflexivity.








(** * Chain goal switching (elements/links -> traces) and a tactic on traces *)

(** *** On elements (singletons, then pairs) *)

Ltac in_modelElements_singleton_fw_tac r_num pat_num i :=
  match goal with 
    [ |- List.In _ (Model.modelElements (Semantics.execute ?T _)) ] =>

      apply <- SemanticsTools.in_modelElements_inv ; 

      eexists ; exists i ; eexists ; eexists ; 

      in_compute_trace_inv_singleton_fw r_num pat_num ;

      try reflexivity
  end.


Ltac in_modelElements_pair_fw_tac r_num pat_num i:=
  match goal with 
    [ |- In _ (modelElements (execute _ _)) ] =>

      apply <- SemanticsTools.in_modelElements_inv ; 

      eexists ; exists i ; eexists ; eexists ; 

      in_compute_trace_inv_pair_fw r_num pat_num ;

      try reflexivity 
  end.

(** *** On links (singleton), two versions *)

Ltac transform_link_fw_tac_singleton r_num pat_num i :=
  match goal with
    [ |- In _ (Semantics.execute _ _).(modelLinks) ] =>

      apply <- SemanticsTools.in_modelLinks_inv ; 
      
      eexists ; exists i ; eexists ; eexists ; eexists ; 

      split ; 
      
      [ in_compute_trace_inv_singleton_fw r_num pat_num | ] ;
      
      autounfold with 
        parse 
        ConcreteOutputPatternUnit_accessors 
        opu_accessors 
  end.

(* Variant where the first rule that don't lead to an error is selected intead of relying on an user hint. *)
Ltac transform_link_fw_tac_singleton_auto i :=
  match goal with
    [ |- In _ (Semantics.execute _ _).(modelLinks) ] =>

      apply <- SemanticsTools.in_modelLinks_inv ; 

      eexists ; exists i ; eexists ; eexists ; eexists ; 
      
      split ;

      [ in_compute_trace_inv_singleton_fw_auto | ] ;
  
      (* Fail if one of the goal reduces to False 
         (trigger backtracking)                   *)
      TacticUtils.fail_on_False ;   
  
      autounfold with 
        parse 
        ConcreteOutputPatternUnit_accessors 
        opu_accessors 
        
  end.




(** * Simple or deprecated tactics *)


(* USED *)
(* Deprecated : use Semantics.in_modelElements_inv instead. *)
Corollary in_trace_in_models_target {MM1:Metamodel} {T1} {T2} {BEQ} :
  forall 
    (t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ)))
    m s e,
    In {| 
        PoorTraceLink.source := s ;
        PoorTraceLink.produced := e
      |}
      (RichTraceLink.drop (compute_trace t m)) ->
    In e (execute t m).(modelElements).
Proof. 
  intros.
  apply RichTraceLink.in_drop_inv in H. simpl in H. destruct H as (? & ?).

  apply SemanticsTools.in_modelElements_inv. 
  unfold RichTraceLink.convert in H. 
  destruct s as ((?&?)&?). 
  eauto.
Qed.



(** * Simple tactics (for simple situations) *)

(** A simple FW tactic for elements (lemma + tactic) (only singleton patterns).

 The drawback of this lemma/tactic is that when the traceTrOnPiece premise is not solved by auto, it leaves the user with a painful subgoal. *)
Lemma transform_element_fw {tc} (t:Syntax.Transformation (tc:=tc)) cm e te  :
  0 < Syntax.arity t ->
  In e (modelElements cm) ->
  In te (produced_elements (traceTrOnPiece t cm [e])) ->
  In te (modelElements (execute t cm)).
Proof.
  intros A IN1 IN2.
  simpl.
  unfold compute_trace, produced_elements.
  rewrite map_flat_map. (* a trace can have several target elements *)
  apply List.in_flat_map. (* this is doing the job *)
  exists ([e]) ; split ; [ | auto ].
  apply <- SemanticsTools.in_allTuples_incl_singleton. auto.
Qed.

(* Used in Class2Relational *)
Ltac transform_element_fw_tac :=
  match goal with
    [ |- In _ (execute ?T _).(modelElements) ] =>
      eapply (transform_element_fw T) ; [ solve [simpl ; auto ] | try eassumption | try (solve [simpl;auto])]
  end.

