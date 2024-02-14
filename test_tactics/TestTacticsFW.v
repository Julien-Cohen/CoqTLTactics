Require Import  TestUtils.


Require TacticsFW.


Import 
  List Model String NotationUtils Semantics PoorTraceLink  NotationUtils Semantics.

Require Import BasicMetamodel.

Open Scope string_scope.




(** Test 1. *)
(** Tactic under test : [TacticsFW.in_compute_trace_inv_singleton_fw] *)
(** Test case : no guard, and the right-hand side of the rule is local *)

Require Import (* fixme : retirer l'Import *) IdTransformation.

Goal 
  forall (m : BasicMetamodel.M)
         (s : BasicMetamodel.Node_t)
         (IN1 : In (Node s) (modelElements m)),
  exists p, 
     @In (@TraceLink.TraceLink IdTransformation.Id_TransformationConfiguration)
      {|
        TraceLink.source := ([Node s], 0, "s");
        TraceLink.produced := Node s;
        TraceLink.linkPattern := p
      |} (compute_trace IdTransformation.T m)
.
Proof.
  idtac "Testing TacticsFW.in_compute_trace_inv_singleton_fw".
  idtac "Test case : the convenient assumption is in the context.".

  intros. eexists.

(* Success of the tactic expected *)
  Succeed
    tryif  
      solve [
          TacticsFW.in_compute_trace_inv_singleton_fw "state" "s" IN1 ;
          reflexivity ]  
    then test_success
    else test_failure.

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


(** Test 2. *)
(** Tactic under test : TacticsFW.in_compute_trace_inv_singleton_fw *)
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
  Succeed 
    tryif 
      solve [TacticsFW.in_compute_trace_inv_singleton_fw "state" "s" H2 ; reflexivity]  
    then test_success
    else test_failure.

  (* Failure of the tactic expected with incorrect parameters *)
  Succeed 
    tryif 
      solve [TacticsFW.in_compute_trace_inv_singleton_fw "state" "s" H1] 
    then test_failure
    else test_success.

Abort.


(** Test 3 *)
(** Tactic under test : TacticsFW.in_modelElements_singleton_fw_tac *)
(** Test case : choice between two assumptions *)
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
  Succeed 
    tryif
      solve [TacticsFW.in_modelElements_singleton_fw_tac "state" "s" 0 H2 ; reflexivity ]  
    then test_success
    else test_failure.

  (* Failure of the tactic expected *)
  Succeed 
    tryif
      TacticsFW.in_modelElements_singleton_fw_tac "state" "s" 0 H1 ; reflexivity
    then test_failure
    else test_success.

Abort.


(** Test 4 *)
(** Tactic under test : TacticsFW.in_modelElements_singleton_fw_tac *)
(** Test case : rules with several output patterns *)

Require DoubleTransformation.

Goal
forall 
  (cm : BasicMetamodel.M)
  
  (H : In
          (BasicMetamodel.Arrow {| Arrow_id := 1 |})
          (modelElements cm)),

  In (BasicMetamodel.Arrow {| Arrow_id := 1 |}) (* same id *)
    (modelElements (execute DoubleTransformation.T cm)).
Proof.
  idtac "Testing TacticsFW.in_modelElements_singleton_fw_tac".
  idtac "Test case : rules with several output patterns (first pattern).".

  intros.


  (* Success of the tactic expected *)
  Succeed 
    tryif
      solve [TacticsFW.in_modelElements_singleton_fw_tac "transition" "t" 0 H ; reflexivity ]  (* second rule, first pattern, it-count=0 *)
    then test_success
    else test_failure.
  
  (* Failure of the tactic expected *)
  Succeed 
    tryif 
      solve [TacticsFW.in_modelElements_singleton_fw_tac "transition" "back_t" 0 H ; reflexivity]  (* second rule, second pattern, it-count=0 *)
    then test_failure
    else test_success.

Abort.


Goal
forall 
  (cm : BasicMetamodel.M)
  
  (H : In
          (BasicMetamodel.Arrow {| Arrow_id := 1 |})
          (modelElements cm)),

  In (BasicMetamodel.Arrow {| Arrow_id := 2 |}) (* id incremented *)
    (modelElements (execute DoubleTransformation.T cm)).
Proof.
  idtac "Testing TacticsFW.in_modelElements_singleton_fw_tac".
  idtac "Test case : rules with several output patterns (second pattern).".

  intros.

  (* Success of the tactic expected *)
  Succeed 
    tryif
      solve [TacticsFW.in_modelElements_singleton_fw_tac "transition" "back_t" 0 H ; reflexivity ] (* second rule, second pattern, it-count = 0 *)
    then test_success
    else test_failure.

  (* Failure of the tactic expected *)
  Succeed 
    tryif
      TacticsFW.in_modelElements_singleton_fw_tac "transition" "t" 0 H ; reflexivity (* failure comes frome reflexivity, not from the tactic *)
    then test_failure
    else test_success.

Abort.


(** FIXME : Not tested : iteration-count > 0 *) 

(** FIXME : Not tested : guards that depend on the model *)

(** FIXME : Not tested : pair patterns *)
