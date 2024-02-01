Require Import IdTransformation TestUtils.

Require TacticsFW.


Import 
  List Model String NotationUtils Semantics PoorTraceLink  NotationUtils Semantics.

Import BasicMetamodel.





(* Test 1. *)
(* Tactic under test : [TacticsFW.in_compute_trace_inv_singleton_fw] *)
(* Test case : no guard, and the right-hand side of the rule is local *)
Goal 
  forall (m : BasicMetamodel.M)
         (s : BasicMetamodel.Node_t)
         (IN1 : In (Node s) (modelElements m)),
  exists p, 
     @In (@TraceLink.TraceLink IdTransformationConfiguration)
      {|
        TraceLink.source := ([Node s], 0, "s"%string);
        TraceLink.produced := Node s;
        TraceLink.linkPattern := p
      |} (compute_trace T m)
.
Proof.
  idtac "Testing TacticsFW.in_compute_trace_inv_singleton_fw".
  idtac "Test case : the convenient assumption is in the context.".

  intros. eexists.

(* Success of the tactic expected *)
  Succeed (first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw 1 1 IN1 ;
             reflexivity ] ; 
      test_success
    | test_failure]).

(* Failure of the tactic expected with incorrect parameters *)
 Succeed first [
      TacticsFW.in_compute_trace_inv_singleton_fw 2 1 IN1 ; 
      test_failure 
    | test_success].

 Succeed first [
      TacticsFW.in_compute_trace_inv_singleton_fw 1 2 IN1 ; 
      test_failure 
    | test_success].

 Succeed first [
      TacticsFW.in_compute_trace_inv_singleton_fw 0 0 IN1 ; 
      test_failure 
    | test_success].
 
 Succeed first [
      TacticsFW.in_compute_trace_inv_singleton_fw 0 1 IN1 ; 
      test_failure 
    | test_success].

 Succeed first [
      TacticsFW.in_compute_trace_inv_singleton_fw 1 0 IN1 ; 
      test_failure 
    | test_success].

Abort.





(* Test 2. *)
(* Tactic under test : TacticsFW.in_compute_trace_inv_singleton_fw *)
Goal 
  forall 
    (cm : M)
    (H1 : In (Node {| Node_id := 1 |}) (modelElements cm))
    (H2 : In (Node {| Node_id := 2 |}) (modelElements cm)),
    
  exists
    (s : list TransformationConfiguration.SourceElementType) 
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
  idtac "Test case : choice between two assumptions.".
  
  eexists ; eexists ; eexists. 

  (* Success of the tactic expected *)
  Succeed (first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw 1 1 H2 ; reflexivity] ; 
      test_success
    | test_failure]).

  (* Failure of the tactic expected with incorrect parameters *)
  Succeed (first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw 1 1 H1] ; 
      test_failure
    | test_success]).

Abort.

(* Test 3 *)
(* Tactic under test : TacticsFW.in_modelElements_singleton_fw_tac *)
(* Test case : choice between two assumptions *)
Goal
forall 
  (cm : BasicMetamodel.M)
  
  (H1 : In
          (BasicMetamodel.Node {| Node_id := 1 |})
          (modelElements cm))
  (H2 : In (BasicMetamodel.Node {| Node_id := 2 |})
         (modelElements cm)),

  In (BasicMetamodel.Node {| Node_id := 2 |})
    (modelElements (execute T cm)).
Proof.
  idtac "Testing TacticsFW.in_modelElements_singleton_fw_tac".
  idtac "Test case : choice between two assumptions.".

  intros.

  (* Success of the tactic expected *)
  Succeed (first [
      solve [TacticsFW.in_modelElements_singleton_fw_tac 1 1 0 H2 ; reflexivity ] ; 
      test_success
    | test_failure]).

  (* Failure of the tactic expected *)
  Succeed (first [
      solve [TacticsFW.in_modelElements_singleton_fw_tac 1 1 0 H1] ; 
      test_failure
    | test_success]).

Abort.



(* Not tested : rules with several output patterns *)

(* Not tested : iteration-count > 0 *) 

(* Not tested : guards that depend on the model *)
