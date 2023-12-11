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

(** * Tactics on traces *)

(** ** Tactics that fully unfold [In _ compute_trace _ _] and solve easy goals. *) 

 Ltac in_compute_trace_inv_singleton_fw r_num pat_num :=
  match goal with 
  | [ |- List.In _ (Semantics.compute_trace ?T _)] => 
      rewrite SemanticsTools.in_compute_trace_inv ; 
      split ; 
      [ | split ;
          [ | eexists ; split ; 
              [ | split ; 
                  [ | split ;
                      [ | eexists ; split 
                          ; [ | ]]]]]] ; 
      
      (* fix the rule under concern following user hint *)
      only 3 : solve [TacticUtils.rule_number r_num] (* no backtrack needed *) ;

      (* fix the output pattern in the rule following user hint *)
      only 5 : solve [TacticUtils.pattern_number pat_num] ;

      (* fix the source piece using the context (singleton version) *)
      only 1 : apply ListUtils.incl_singleton ;
      only 1 : TacticUtils.multi_eassumption (* backtrack point *); 

      (* ensure that the instantiation made at the prevous step is type-safe, otherwise backtrack *)
      only 2 : (* guard *) TacticUtils.fail_on_type_mismatch ; 

      only 2 : (* guard *) simpl ;
      only 1 : (* arity *) solve [simpl ; auto] ; (* solve the arity contraint (the input is fixed) *)
      only 2 : (* iteration_counter *) solve [simpl ; auto] ;
      only 2 : (* make_element *) simpl ;
      try reflexivity (* solves simple evalGguard & make_element goals *)
  end.

(* variant that tries to guess the rule and the pattern *)
(*FIXME : test-me more *)
Ltac in_compute_trace_inv_singleton_fw_auto := 
  setoid_rewrite SemanticsTools.in_compute_trace_inv (*in the left part*) ;
  split ; 
  [ (*1*) 
  | split ; 
    [ (* 2 *)
    |  eexists ; split ; 
       [ (* 3 *) 
       | split ;
         [(* 4 *)
         | split ;
           [ (* 5 *) 
           |  eexists ; split ; 
              [ (*6*) 
              | (*7*)] ]]] ] ] ;
  
  
  (* fix the rule under concern (try and backtrack) *)
  only 3: (TacticUtils.first_rule + TacticUtils.second_rule) ;
  
  (* fix the output pattern in the rule (try and backtrack) *)
  only 5 : (TacticUtils.first_in_list + TacticUtils.second_in_list) ;
  
  (* fix the source piece using the context *)
  only 1 : solve [TacticUtils.incl_singleton] ; (* this works only for singletons *)
  
  (* solve the arity contraint (the input is fixed) *)
  only 1 : solve [simpl;auto] ;
  
  (* Solve the guard (the input is fixed) *)
  (* If the user has selected the correct rule, the match guard should evaluate to true *)
  only 1 : reflexivity ; (* fixme : fail when the guard is complex *) 
  
  (* solve the iteration contraint *)
  only 1 : solve [ simpl ; auto]
.

(* variant for pair patterns *)
Ltac in_compute_trace_inv_pair_fw r_num pat_num :=
  match goal with 
  | [ |- List.In _ (Semantics.compute_trace ?T _)] => 
        rewrite SemanticsTools.in_compute_trace_inv ; 
    split ; [ | split ; [ | eexists ; split ; [ | split ; [ | split ; [ | eexists ; split ; [ | ]]]]]] ; 
      only 3 : solve [TacticUtils.rule_number r_num] (* no backtrack needed *) ;
        only 5 : solve [TacticUtils.pattern_number pat_num] ;
        only 1 : (apply ListUtils.incl_pair ; split)  ;
        only 3 : solve [compute ; auto] ;
        only 3 : simpl ;
        only 4 : solve [compute ; auto] ;
        only 4 : simpl ;
        only 1 : TacticUtils.multi_eassumption (* backtrack point *);
        only 1 : TacticUtils.multi_eassumption (* backtrack point *); (* fragile : does not backtrack in used as follows ; apply ListUtils.incl_pair ; split ; multi_eassumption *)
        only 1 : TacticUtils.fail_on_type_mismatch ;

        try reflexivity
  end.





(** * Switch from a goal on elements/links to a goal on traces *)

Ltac in_modelLinks_inv_split_fw i :=
  match goal with
    [ |- In _ (Semantics.execute _ _).(modelLinks) ] =>
      apply <- SemanticsTools.in_modelLinks_inv ; 
      eexists ; exists i ; eexists ; eexists ; eexists ; split
  end.

Ltac in_modelElements_inv_split_fw i :=
  match goal with 
    | [ |- List.In _ (Semantics.execute _ _).(Model.modelElements)] =>
      apply <- SemanticsTools.in_modelElements_inv ; 
      eexists ; exists i ; eexists ; eexists 
  end.




(** * Chain goal switching (elements/links -> traces) and a tactic on traces *)

(** *** On elements (singleton, then pairs) *)

Ltac in_modelElements_singleton_fw_tac r_num pat_num i :=
  match goal with 
    [ |- List.In _ (Model.modelElements (Semantics.execute ?T _)) ] =>
      in_modelElements_inv_split_fw i ; 
      in_compute_trace_inv_singleton_fw r_num pat_num ;
      try reflexivity
  end.


Ltac in_modelElements_pair_fw_tac r_num pat_num i:=
  match goal with 
    [ |- In _ (modelElements (execute _ _)) ] =>
      TacticsFW.in_modelElements_inv_split_fw i ;
      in_compute_trace_inv_pair_fw r_num pat_num ;
      try reflexivity 
  end.

(** *** On links (singleton), two versions *)

Ltac transform_link_fw_tac_singleton r_num pat_num i :=
  match goal with
    [ |- In _ (Semantics.execute _ _).(modelLinks) ] =>
      in_modelLinks_inv_split_fw i;

      [ in_compute_trace_inv_singleton_fw r_num pat_num | ] ;
      autounfold with 
        parse 
        ConcreteOutputPatternUnit_accessors 
        opu_accessors 
  end.

(* variant where the first rule that don't lead to an error is selected intead of relying on an user hint *)
Ltac transform_link_fw_tac_singleton_auto i :=
  match goal with
    [ |- In _ (Semantics.execute _ _).(modelLinks) ] =>

      in_modelLinks_inv_split_fw i;

      [in_compute_trace_inv_singleton_fw_auto | ] ;
      
      try reflexivity ;
      autounfold with 
        parse 
        ConcreteOutputPatternUnit_accessors 
        opu_accessors  ;
      
      (* fail if one of the goal reduces to False *)
      tryif simpl ; match goal with [ |- False] => idtac end then fail else idtac  

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
  apply <- in_allTuples_incl_singleton. auto.
Qed.

(* Used in Class2Relational *)
Ltac transform_element_fw_tac :=
  match goal with
    [ |- In _ (execute ?T _).(modelElements) ] =>
      eapply (transform_element_fw T) ; [ solve [simpl ; auto ] | try eassumption | try (solve [simpl;auto])]
  end.

