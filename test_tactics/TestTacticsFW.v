Require Import  TestUtils.


Require TacticsFW.


Import 
  List Model String NotationUtils Semantics PoorTraceLink  NotationUtils.

Open Scope string_scope.

From test_tactics
  Require BasicMetamodel IdTransformation DoubleTransformation.

Require Class2Relational.Class2Relational.


(** Tests for tactics on elements. *)

Section Test1.

(** Tactic under test : [TacticsFW.in_compute_trace_inv_singleton_fw] *)
(** Test case : no guard, and the right-hand side of the rule is local *)

Import BasicMetamodel IdTransformation.

(* Preparation of data. *)

(* The transformation. *)
Definition T := IdTransformation.T.

(* The link_producer in the "state" rule of the transformation. *)
Definition T_state_link_producer:Syntax.link_producer.
  remember T.(Syntax.rules) as r.
  destruct r eqn:? ; [discriminate | ].
  destruct r0 eqn:?.
  destruct r_outputPattern eqn:? ; [ discriminate | ].
  destruct o eqn:?.
  exact opu_link.
Defined.

(* Preparation of the goal *)
Context 
  (m : M) 
  (s : Node_t) 
  (IN1 : In (Node s) (modelElements m)).

Goal 
     In
      {|
        TraceLink.source := ([Node s], 0, "s");
        TraceLink.produced := Node s;
        TraceLink.linkPattern := T_state_link_producer
      |} 
      (compute_trace T m).
Proof.
  idtac "Testing TacticsFW.in_compute_trace_inv_singleton_fw".
  idtac "Test case : the convenient assumption is in the context and convenient parameters are given to the tactic.".

  (* Execution of the tactic.*)

  Succeed
    tryif
      TacticsFW.in_compute_trace_inv_singleton_fw "state" "s" IN1 ;

      (* Oracle *)

      (* 1) the tactic should not fail *)

      (* 2) The tactic should leave 2 subgoals *)
      [ | ] ;

      (* 3) The first subgoal must have a given shape. *)
      only 1:
        match goal with 
        | [ |- ConcreteExpressions.makeEmptyGuard [Node_K] m [Node s] = true ] => 
            idtac
        | _ =>
            fail
        end ;
      
      (* 4) The second subgoal must have a given shape. *)
      only 2 : 
        match goal with
        | [ |- ConcreteExpressions.makeElement [Node_K] Node_K _ 0 m [Node s] = return Node s ] =>
            idtac 
        | _ =>
            fail 
        end
          
        
    then test_success
    else test_failure.
  
  
  idtac "Test case : the convenient assumption is in the context but incorrect parameters are given to the tactic.".

(* Failure of the tactic expected with incorrect parameters *)
 Succeed 
   tryif
     TacticsFW.in_compute_trace_inv_singleton_fw "transition" "s" IN1 
   then test_failure 
   else test_success.

 Succeed 
   tryif
      TacticsFW.in_compute_trace_inv_singleton_fw "state" "t" IN1  
   then test_failure 
   else test_success.

 Succeed 
   tryif 
     TacticsFW.in_compute_trace_inv_singleton_fw "_" "_" IN1  
   then test_failure 
   else test_success.
 
 Succeed 
   tryif 
     TacticsFW.in_compute_trace_inv_singleton_fw "_" "s" IN1 
   then test_failure 
   else test_success.

 Succeed 
   tryif 
     TacticsFW.in_compute_trace_inv_singleton_fw "state" "_" IN1  
   then test_failure 
   else test_success.

Abort.

End Test1. 


Section Test2.

(** Tactic under test : TacticsFW.in_compute_trace_inv_singleton_fw *)

Import BasicMetamodel IdTransformation.

Context
    (cm : M)
    (H1 : In (Node {| Node_id := 1 |}) (modelElements cm))
    (H2 : In (Node {| Node_id := 2 |}) (modelElements cm)).

Goal    
  exists
    (s : list Element) 
    (n : string) 
    lp,
    In
      {|
        TraceLink.source := (s, 0, n);
        TraceLink.produced := Node {| Node_id := 2 |};
        TraceLink.linkPattern := lp
      |} (compute_trace T cm)
.
Proof.
  idtac "Testing TacticsFW.in_compute_trace_inv_singleton_fw".
  idtac "Test case : choice between two assumptions (with correct parameters).".
  
  eexists ; eexists ; eexists. 

  (* Success of the tactic expected *)
  Succeed 
    tryif 
      TacticsFW.in_compute_trace_inv_singleton_fw "state" "s" H2 ;
      reflexivity  
    then test_success
    else test_failure.

  idtac "Test case : choice between two assumptions (with incorrect parameters).".

  (* Failure of the tactic expected with incorrect parameters *)
  Succeed
    tryif 
      TacticsFW.in_compute_trace_inv_singleton_fw "state" "s" H1 ;
      reflexivity  (* the tactic works but an incorrect hypothesis was selected, so that the goal cannot be solved anymore *)
    then test_failure
    else test_success.

Abort.

End Test2.


Section Test3.

(** Tactic under test : TacticsFW.in_modelElements_singleton_fw_tac *)
(** Test case : choice between two assumptions *)

Import BasicMetamodel IdTransformation.

Context 
  (cm : M)
  (H1 : In (Node {| Node_id := 1 |}) (modelElements cm))
  (H2 : In (Node {| Node_id := 2 |}) (modelElements cm)).

Goal
  In (Node {| Node_id := 2 |}) (modelElements (execute T cm)).

Proof.
  idtac "Testing TacticsFW.in_modelElements_singleton_fw_tac".
  idtac "Test case : choice between two assumptions (with correct parameters).".

  (* Success of the tactic expected *)
  Succeed 
    tryif
      TacticsFW.in_modelElements_singleton_fw_tac "state" "s" 0 H2 ;
      reflexivity   
    then test_success
    else test_failure.
 
  idtac "Test case : choice between two assumptions (with incorrect parameters).".

  (* Failure of the tactic expected *)
  Succeed 
    tryif
      TacticsFW.in_modelElements_singleton_fw_tac "state" "s" 0 H1 ;
      reflexivity
    then test_failure
    else test_success.

Abort.

End Test3.


Section Test4.

(** Tactic under test : TacticsFW.in_modelElements_singleton_fw_tac *)
(** Test case : rules with several output patterns *)

  Import  BasicMetamodel DoubleTransformation.

  Context
    (cm : M)
    (H : In (Arrow {| Arrow_id := 1 |}) (modelElements cm)).

  Goal
    In (Arrow {| Arrow_id := 1 |}) (modelElements (execute T cm)).
  
  Proof.
    idtac "Testing TacticsFW.in_modelElements_singleton_fw_tac".
    idtac "Test case : rules with several output patterns (first pattern, correct parameters).".
    
    (* Success of the tactic expected *)
    Succeed 
      tryif
        TacticsFW.in_modelElements_singleton_fw_tac "transition" "t" 0 H ; (* second rule, first pattern, it-count=0 *)
        reflexivity   
      then test_success
      else test_failure.

     idtac "Test case : rules with several output patterns (first pattern, incorrect parameters).".
   
    (* Failure of the tactic expected *)
    Succeed 
      tryif 
        TacticsFW.in_modelElements_singleton_fw_tac "transition" "back_t" 0 H ; (* second rule, second pattern, it-count=0 *)
      reflexivity  
      then test_failure
      else test_success.
    
  Abort.

End Test4.


Section Test5.

Import BasicMetamodel DoubleTransformation.

Context
  (cm : M)
    (H : In (Arrow {| Arrow_id := 1 |}) (modelElements cm)).

Goal
  In 
    (Arrow {| Arrow_id := 2 |}) (* id incremented *)
    (modelElements (execute T cm)).
Proof.
  idtac "Testing TacticsFW.in_modelElements_singleton_fw_tac".
  idtac "Test case : rules with several output patterns (second pattern, correct parameters).".

  (* Success of the tactic expected *)
  Succeed 
    tryif
      TacticsFW.in_modelElements_singleton_fw_tac "transition" "back_t" 0 H ; (* second rule, second pattern, it-count = 0 *)
      reflexivity 
    then test_success
    else test_failure.

  idtac "Test case : rules with several output patterns (second pattern, incorrect parameters).".

  (* Failure of the tactic expected *)
  Succeed 
    tryif
      TacticsFW.in_modelElements_singleton_fw_tac "transition" "t" 0 H ; (* failure comes frome reflexivity, not from the tactic *)
      reflexivity 
    then test_failure
    else test_success.

Abort.

End Test5.

(** FIXME : Not tested : iteration-count > 0 *) 

(** FIXME : Not tested : guards that depend on the model *)

(** FIXME : Not tested : pair patterns *)



(** Tests for tactics on links. *)
 
Section TestLink1.

Import Glue ClassMetamodel RelationalMetamodel Class2Relational.

Context
 (cm : ClassModel)
  (i : nat)(i' : nat)
  (n : string)(n' : string)
  
  (IN : 
    In (AttributeElement 
          {| 
            Attribute_id := i ;
            Attribute_derived := false ;
            Attribute_name := n
          |})
      (modelElements cm)).

Goal    
    In
      (Column_referenceLink
         (glue {| Column_id := i ; Column_name := n |} 
           with {| Table_id := i'; Table_name := n' |}))
    (modelLinks (execute Class2Relational cm)).
Proof. 
  idtac "Testing TacticsFW.transform_link_fw_tac_singleton".
  idtac "Test case : ".

  tryif
    TacticsFW.transform_link_fw_tac_singleton "Attribute2Column" "col" 0 IN ;

    (* Oracle. *)
    
    (* 1) The tactic should no fail. *)

    (* 2) There should be 3 subgoals. *)

    [ | | ] ;
    
     (* 3) The first goal must be a makeGuard. *)
    only 1 :  
      match goal with 
      | [ |- ConcreteExpressions.makeGuard _ _ _ _ = true] => idtac 
      | _ => fail 
      end ;
    
    (* 4) The second subgoal should be a makeElement. *) 
    only 2 :
      match goal with 
      | [ |- ConcreteExpressions.makeElement _ _ _ _ _ _ = Some _] => idtac
      | _ => fail 
      end   ;
    
    
    (* 5) The third goal must have the following shape. *)
    only 3 :
      match goal with 
      | [ |- In 
               (Column_referenceLink _) 
               (apply_link_pattern (compute_trace Class2Relational cm) cm _) ] => 
          idtac 
            
      | [ |- _] => fail 
      end    

  then test_success
  else test_failure.


Abort.


End TestLink1.
