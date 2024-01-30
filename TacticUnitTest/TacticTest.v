Require Import IdTransformation.

Require TacticsFW.


Import 
  List Model String NotationUtils Semantics PoorTraceLink  NotationUtils Semantics.

Import BasicMetamodel.

Ltac test_success := idtac "Test succeeded.".
Ltac test_failure := 
  idtac " ";
  idtac "========================" ;
  idtac "===== Test Failed. =====" ;
  idtac "========================" ;
  idtac " ".


(** Tactic under test : [TacticsFW.in_compute_trace_inv_singleton_fw] *)

(* Test 1. *)
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

(* Success of the tactid expected *)
  Succeed (first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw 1 1] ; 
      test_success
    | test_failure]).

(* Failure of the tactic expected *)
 Succeed first [
      TacticsFW.in_compute_trace_inv_singleton_fw 2 1 ; 
      test_failure 
    | test_success].

 Succeed first [
      TacticsFW.in_compute_trace_inv_singleton_fw 1 2 ; 
      test_failure 
    | test_success].

 Succeed first [
      TacticsFW.in_compute_trace_inv_singleton_fw 0 0 ; 
      test_failure 
    | test_success].
 
 Succeed first [
      TacticsFW.in_compute_trace_inv_singleton_fw 0 1 ; 
      test_failure 
    | test_success].

 Succeed first [
      TacticsFW.in_compute_trace_inv_singleton_fw 1 0 ; 
      test_failure 
    | test_success].

Abort.



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
  idtac "Test case : choice between two assumptions (1/2).".

  intros.

  (* Success of the tactid expected *)
  Succeed (first [
      solve [TacticsFW.in_modelElements_singleton_fw_tac 1 1 0] ; 
      test_success
    | test_failure]).

Abort.

Goal
forall 
  (cm : BasicMetamodel.M)
  
  (H1 : In
          (BasicMetamodel.Node {| Node_id := 2 |})
          (modelElements cm))
  (H2 : In (BasicMetamodel.Node {| Node_id := 1 |})
         (modelElements cm)),

  In (BasicMetamodel.Node {| Node_id := 2 |})
    (modelElements (execute T cm)).
Proof.
  idtac "Testing TacticsFW.in_modelElements_singleton_fw_tac".
  idtac "Test case : choice between two assumptions (2/2).".

  intros.

  (* Success of the tactid expected *)
  Succeed (first [
      solve [TacticsFW.in_modelElements_singleton_fw_tac 1 1 0] ; 
      test_success
    | test_failure]).

Abort.



(* Test case : Choose between two assumptions. *)

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
  idtac "Test case : choice between two assumptions. (1/2)".
  
  eexists ; eexists ; eexists. 

  (* Success of the tactid expected *)
  Succeed (first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw 1 1] ; 
      test_success
    | test_failure]).

Abort.


Goal forall (cm : M)
  (H1 : In (Node {| Node_id := 2 |}) (modelElements cm))
  (H2 : In (Node {| Node_id := 1 |}) (modelElements cm)),
  
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
  idtac "Test case : choice between two assumptions. (2/2)".

      eexists ; eexists ; eexists. 

  (* Success of the tactid expected *)
  
      TacticsFW.in_compute_trace_inv_singleton_fw 1 1 .

      compute.
      f_equal.
      f_equal.
      f_equal. (* The wrong assumption has been selected, and the goal cannot be solved anymore. *)

      first [reflexivity ; test_success | test_failure].

      (* this failure is solved with the adapted tactic [TacticsFW.in_compute_trace_inv_singleton_fw_solve], see below. *)
Abort.


(* Test the re-ordered tactic (second solving tactic). *)

Goal forall (cm : M)
  (H1 : In (Node {| Node_id := 2 |}) (modelElements cm))
  (H2 : In (Node {| Node_id := 1 |}) (modelElements cm)),
  
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
  idtac "Testing TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered".
  idtac "Test case : choice between two assumptions. (1/2)".


      eexists ; eexists ; eexists. 

  (* Success of the tactid expected *)
  Succeed (first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 1 1] ; 
      test_success
    | test_failure]).


  (* Failure of the tactic expected *)
  Succeed first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 2 1] ; 
      test_failure 
    | test_success].

   (* Failure of the tactic expected *)
  Succeed first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 1 2] ; 
      test_failure 
    | test_success].
      
Abort.


(* re-ordered lemma/tactic *)
Goal forall (cm : M)
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
  idtac "Testing TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered".
  idtac "Test case : choice between two assumptions. (2/2)".


      eexists ; eexists ; eexists. 


  (* Success of the tactid expected *)
  Succeed (first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 1 1] ; 
      test_success
    | test_failure]).


  (* Failure of the tactic expected *)
  Succeed first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 2 1] ; 
      test_failure 
    | test_success].
      
Abort.

 (* Test case : there are links in the rule + local guard *)
Goal forall (cm : M)
  (H1 : In (Arrow {| Arrow_id := 2 |}) (modelElements cm))
  (H2 : In (Arrow {| Arrow_id := 1 |}) (modelElements cm)),
  
  exists
    (s : list TransformationConfiguration.SourceElementType) 
    (n : string)
    lp,
    In
      {|
        TraceLink.source := (s, 0, n);
        TraceLink.produced := Arrow {| Arrow_id := 2 |};
        TraceLink.linkPattern := lp
      |} (compute_trace T cm)
.
Proof.
  idtac "Testing TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered".
  idtac "Test case : choice between two assumptions, local guard. (1/2)".


  eexists ; eexists ; eexists. 

  (* Success of the tactid expected *)
  Succeed (first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 2 1] ; 
      test_success
    | test_failure]).


  (* Failure of the tactic expected *)
  Succeed first [
      TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 1 1 ; 
      test_failure 
    | test_success].

Abort.

(* re-ordered lemma/tactic *)
Goal forall (cm : M)
  (H1 : In (Arrow {| Arrow_id := 1 |}) (modelElements cm))
  (H2 : In (Arrow {| Arrow_id := 2 |}) (modelElements cm)),
  
  exists
    (s : list TransformationConfiguration.SourceElementType) 
    (n : string)
    lp,
    In
      {|
        TraceLink.source := (s, 0, n);
        TraceLink.produced := Arrow {| Arrow_id := 2 |};
        TraceLink.linkPattern := lp
      |} (compute_trace T cm)
.
Proof.
  idtac "Testing TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered".
  idtac "Test case : choice between two assumptions, local guard. (2/2)".

      eexists ; eexists ; eexists. 

  (* Success of the tactid expected *)
  Succeed (first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 2 1] ; 
      test_success
    | test_failure]).


  (* Failure of the tactic expected *)
  Succeed first [
       TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 1 1 ; 
      test_failure 
    | test_success].
      
Abort.


(* Test case : Choose between two assumptions. (solving tactic) *)

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
  idtac "Testing TacticsFW.in_compute_trace_inv_singleton_fw_solve".
  idtac "Test case : choice between two assumptions. (1/2)".

      eexists ; eexists ; eexists. 

  (* Success of the tactid expected *)
  Succeed (first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve 1 1] ; 
      test_success
    | test_failure]).

Abort.

Goal 
  forall 
    (cm : M)
    (H1 : In (Node {| Node_id := 2 |}) (modelElements cm))
    (H2 : In (Node {| Node_id := 1 |}) (modelElements cm)),
  
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
  idtac "Testing TacticsFW.in_compute_trace_inv_singleton_fw_solve".
  idtac "Test case : choice between two assumptions. (2/2)".

      eexists ; eexists ; eexists. 

  (* Success of the tactid expected *)
  Succeed (first [
      solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve 1 1] ; 
      test_success
    | test_failure]).

Abort.

(* Not tested : rules with several output patterns *)

(* Not tested : iteration-count > 0 *) 

(* Not tested : guards that depend on the model *)
