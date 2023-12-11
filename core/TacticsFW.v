Require Import core.Semantics.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Require Certification.

Import Metamodel Model.

#[global]
Hint Unfold 
  Semantics.traceTrOnPiece 
  Semantics.traceRuleOnPiece 
  Semantics.traceIterationOnPiece 
  Semantics.traceElementOnPiece 
  Semantics.produced_elements 
  : trace.

#[global]
Hint Unfold 
  Semantics.execute 
  Semantics.compute_trace 
  Semantics.produced_elements : semantics.


(** *** Utilities *)

(** When we know which rule is the one we search, the following tactics help us to say it. 

In particular in the case we have an existential variable in the goal, as in [In ?r (Syntax.rules Class2Relational)]
(after use of [in_compute_trace_inv]).

*)
Lemma In_1 {A} :
      forall (e:A) s,
      (exists r, s = e :: r) -> In e s.
Proof.
  intros e s (r&E) ; subst s. 
  apply in_eq.
Qed.

Ltac first_in_list :=
  match goal with 
    [ |- In _ _ ] =>
      apply In_1 ; eexists ; reflexivity
  end.

Ltac first_rule :=
  match goal with 
    [ |- In _ (Syntax.rules _)] =>
      first_in_list
  end.

Lemma In_2 {A} :
      forall (e:A) s,
      (exists a r, s = a :: e :: r) -> In e s.
Proof.
  intros e s (a&r&E) ; subst s. 
  apply in_cons. apply in_eq.
Qed.

Ltac second_in_list :=
  match goal with 
    [ |- In _ _ ] =>
      apply In_2 ; eexists ; eexists ; reflexivity
  end.


Ltac second_rule :=
  match goal with 
    [ |- In _ (Syntax.rules _)] =>
      second_in_list
  end.



Ltac multi_eassumption :=
    multimatch goal with
      | [ H : In _ (modelElements _) |- _ ] => exact H 
    end.

Ltac incl_singleton :=
  apply ListUtils.incl_singleton ; 
  multimatch goal with
    [ H : List.In _ _ |- _ ] => exact H 
                            
    (* multimatch is important here because it allows backtracking, as opposed to eassumption. Here, if there are two hypothesis in the context that allow to solve the goal, because of evar in the goal, if the the selected hypothesis instanciates the evar so that the following tactics fail, it will backtrack and select another one.  This situation can be explored in the proof of Moore2MEaly/theorems/Links/source_link_fw (use move to switch the order of hypothesis) *)

  end.

Ltac rule_number n := 
  match n with 
    1 => TacticsFW.first_rule 
  | 2 => TacticsFW.second_rule 
end.

Ltac pattern_number n :=
  match n with 
    1 => TacticsFW.first_in_list 
  | 2 => TacticsFW.second_in_list 
  end.

(* When a guard is applied to an input piece that does not match the explected type, evaluation of the guard will lead to false = true. This tacic detects this situation and fails when it occurs. Such a failure can bu used to trigger a backtrack. *)
Ltac fail_on_type_mismatch :=
(*  match goal with 
    [ |- UserExpressions.evalGuard _ _ _ = true] =>*)
      tryif 
        assert_fails ( 
            compute ;
            lazymatch goal with 
            | [ |- false = true]  => fail 
            | _ => idtac
            end) 
      then fail 
      else idtac
(*  end*).


(** * Tactics on traces *)


(* Fully unfold [In _ compute_trace _ _] and solve easy goals. *) 
 Ltac in_compute_trace_inv_singleton_fw r_num pat_num :=
  match goal with 
  | [ |- List.In _ (Semantics.compute_trace ?T _)] => 
      rewrite Semantics.in_compute_trace_inv ; 
      split ; 
      [ | split ;
          [ | eexists ; split ; 
              [ | split ; 
                  [ | split ;
                      [ | eexists ; split 
                          ; [ | ]]]]]] ; 
      
      only 3 : solve [TacticsFW.rule_number r_num] (* no backtrack needed *) ;
      only 5 : solve [TacticsFW.pattern_number pat_num] ;
      only 1 : apply ListUtils.incl_singleton ;
      only 1 : TacticsFW.multi_eassumption (* backtrack point *); 
      only 2 : (* guard *)TacticsFW.fail_on_type_mismatch ;
      only 2 : (* guard *) simpl ;
      only 1 : (* arity *) solve [simpl ; auto] ;
      only 2 : (* iteration_counter *) solve [simpl ; auto] ;
      only 2 : (* make_element *) simpl ;
      try reflexivity (* guard & make_element *)
  end.



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

  apply in_modelElements_inv. 
  unfold RichTraceLink.convert in H. 
  destruct s as ((?&?)&?). 
  eauto.
Qed.


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



(** *** Complex tactics (singleton patterns)*)

(* FIXME : split into two tactics *)
Ltac transform_link_fw_tac_singleton r_num pat_num i :=
  match goal with
    [ |- In _ (Semantics.execute _ _).(modelLinks) ] =>
      apply <- Semantics.in_modelLinks_inv ;
      setoid_rewrite Semantics.in_compute_trace_inv (*in the left part*) ;
      eexists ; exists i ; eexists ; eexists ; eexists ; (* s i n res and lp from in_modelLinks_inv *)
      split ; [ split ; [ (*1*) | split ; [ (* 2 *)|  eexists ; split ; [ (* 3 *) | split ; [(* 4 *)| split ; [ (* 5 *) |  eexists ; split ; [ (*6*) | (*7*)] ]]] ] ] |  (* 8 *)] ;


      (* fix the rule under concern following user hint *)
      only 3: solve [rule_number r_num] ;

      (* fix the output pattern in the rule following user hint *)
      only 5 : solve [pattern_number pat_num] ;
      
      (* fix the source piece using the context *)
      only 1 : solve [TacticsFW.incl_singleton] ; (* this works only for singletons *)

      (* solve the arity contraint (the input is fixed) *)
      only 1 : solve [simpl;auto] ;

      (* Solve the guard (the input is fixed) *)
      (* If the user has selected the correct rule, the match guard should evaluate to true *)
      only 1 : reflexivity ; (* fixme : fail when the guard is complex *) 
      
      (* solve the iteration contraint *)
      only 1 : solve [ simpl ; auto] ;

      try reflexivity ;
      autounfold with 
        parse 
        ConcreteOutputPatternUnit_accessors 
        opu_accessors  ;
      
      (* fail if one of the goal reduces to False *)
      tryif simpl ; match goal with [ |- False] => idtac end then fail else idtac  

(* FIXME : change the order of the terms in Semantics.in_compute_trace_inv so that the order of the subgoals to solve smartly is left to right *)

  end.

(* This is a variant of the tactic transform_link_fw_tac_singleton where the first rule that don't lead to an error is selected intead of relying on an user hint *)
(* FIXME : split in two tactics *)
Ltac transform_link_fw_tac_singleton_auto i :=
  match goal with
    [ |- In _ (Semantics.execute _ _).(modelLinks) ] =>
      apply <- Semantics.in_modelLinks_inv ;
      setoid_rewrite Semantics.in_compute_trace_inv (*in the left part*) ;
      eexists ; eexists i ; eexists ; eexists ; eexists ;
      split ; [ split ; [ (*1*) | split ; [ (* 2 *)|  eexists ; split ; [ (* 3 *) | split ; [(* 4 *)| split ; [ (* 5 *) |  eexists ; split ; [ (*6*) | (*7*)] ]]] ] ] |  (* 8 *)] ;


      (* fix the rule under concern (try and backtrack) *)
      only 3: (TacticsFW.first_rule + TacticsFW.second_rule) ;

      (* fix the output pattern in the rule (try and backtrack) *)
      only 5 : (TacticsFW.first_in_list + TacticsFW.second_in_list) ;
      
      (* fix the source piece using the context *)
      only 1 : solve [TacticsFW.incl_singleton] ; (* this works only for singletons *)

      (* solve the arity contraint (the input is fixed) *)
      only 1 : solve [simpl;auto] ;

      (* Solve the guard (the input is fixed) *)
      (* If the user has selected the correct rule, the match guard should evaluate to true *)
      only 1 : reflexivity ; (* fixme : fail when the guard is complex *) 
      
      (* solve the iteration contraint *)
      only 1 : solve [ simpl ; auto] ;

      [ | ] ; 
      try reflexivity ;
      autounfold with 
        parse 
        ConcreteOutputPatternUnit_accessors 
        opu_accessors  ;
      
      (* fail if one of the goal reduces to False *)
      tryif simpl ; match goal with [ |- False] => idtac end then fail else idtac  

(* FIXME : change the order of the terms in Semantics.in_compute_trace_inv so that the order of the subgoals to solve smartly is left to right *)

  end.


Ltac in_modelElements_inv_split_fw :=
  match goal with 
    | [ |- List.In _ (Semantics.execute _ _).(Model.modelElements)] =>
      apply <- Semantics.in_modelElements_inv ; 
      eexists ; 
	unshelve eexists ; (* unshelve because the iteration counter is not automatically deduced later, so we have to leave it as an unshelved goal *)
	 [ | eexists ; eexists] ; swap 1 2
  end.




Ltac in_modelElements_singleton_fw_tac r_num pat_num i :=
  match goal with 
    [ |- List.In _ (Model.modelElements (Semantics.execute ?T _)) ] =>
      in_modelElements_inv_split_fw ; 
      [ | exact i] ; 
      in_compute_trace_inv_singleton_fw r_num pat_num ;
      try reflexivity
  end.


(** *** Complex tactics (pair patterns) *)

(* used for pair patterns *)
Ltac in_compute_trace_inv_pair_fw r_num pat_num :=
  match goal with 
  | [ |- List.In _ (Semantics.compute_trace ?T _)] => 
        rewrite Semantics.in_compute_trace_inv ; 
    split ; [ | split ; [ | eexists ; split ; [ | split ; [ | split ; [ | eexists ; split ; [ | ]]]]]] ; 
      only 3 : solve [TacticsFW.rule_number r_num] (* no backtrack needed *) ;
        only 5 : solve [TacticsFW.pattern_number pat_num] ;
        only 1 : (apply ListUtils.incl_pair ; split)  ;
        only 3 : solve [compute ; auto] ;
        only 3 : simpl ;
        only 4 : solve [compute ; auto] ;
        only 4 : simpl ;
        only 1 : TacticsFW.multi_eassumption (* backtrack point *);
        only 1 : TacticsFW.multi_eassumption (* backtrack point *); (* fragile : does not backtrack in used as follows ; apply ListUtils.incl_pair ; split ; multi_eassumption *)
        only 1 : TacticsFW.fail_on_type_mismatch ;

        try reflexivity
  end.

(* used for pair patterns *)
Ltac in_modelElements_pair_fw_tac r_num pat_num i:=
  match goal with 
    [ |- In _ (modelElements (execute _ _)) ] =>
      TacticsFW.in_modelElements_inv_split_fw ;
      [ | exact i] ;
      in_compute_trace_inv_pair_fw r_num pat_num ;
      try reflexivity 
  end.
