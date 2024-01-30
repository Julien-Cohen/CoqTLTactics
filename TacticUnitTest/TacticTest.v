Require Import IdTransformation.

Require TacticsFW.


Import 
  List Model String NotationUtils Semantics PoorTraceLink  NotationUtils Semantics.


Goal 
  forall (m : BasicMetamodel.M)
         (s : BasicMetamodel.Node_t)
         (IN1 : In (BasicMetamodel.Node s) (modelElements m)),
  exists p, 
     @In (@TraceLink.TraceLink IdTransformationConfiguration)
      {|
        TraceLink.source := ([BasicMetamodel.Node s], 0, "s"%string);
        TraceLink.produced := BasicMetamodel.Node s;
        TraceLink.linkPattern := p
      |} (compute_trace T m)
.
Proof.


  intros. eexists.

  Succeed solve [TacticsFW.in_compute_trace_inv_singleton_fw 1 1].

  Fail TacticsFW.in_compute_trace_inv_singleton_fw 2 1.
  Fail TacticsFW.in_compute_trace_inv_singleton_fw 1 2.
  Fail TacticsFW.in_compute_trace_inv_singleton_fw 0 0.
  Fail TacticsFW.in_compute_trace_inv_singleton_fw 0 1.
  Fail TacticsFW.in_compute_trace_inv_singleton_fw 1 0.


Abort.

Import BasicMetamodel.

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
  intros.
  Succeed solve [TacticsFW.in_modelElements_singleton_fw_tac 1 1 0].
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

      eexists ; eexists ; eexists. 

      Succeed solve [TacticsFW.in_compute_trace_inv_singleton_fw 1 1]. 
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

      eexists ; eexists ; eexists. 

   (* FIXME *)   progress TacticsFW.in_compute_trace_inv_singleton_fw 1 1. 
      compute.
      f_equal.
      f_equal.
      f_equal. (* The wrong assumption has been selected, and the goal cannot be solved anymore. *)
      
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

      eexists ; eexists ; eexists. 

   Succeed  solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 1 1]. 
   Fail  solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 2 1]. 
Fail  solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 1 2]. 
      
Abort.

(* second order *)
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

      eexists ; eexists ; eexists. 

   Succeed solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 1 1]. 
   Fail solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 2 1]. 
      
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

      eexists ; eexists ; eexists. 

   Succeed solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 2 1].       
   Fail TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 1 1.       
Abort.

(* second order *)
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

      eexists ; eexists ; eexists. 

   Succeed solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 2 1].
   Fail TacticsFW.in_compute_trace_inv_singleton_fw_solve_reordered 1 1.
      
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

      eexists ; eexists ; eexists. 

      Succeed solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve 1 1]. 
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

      eexists ; eexists ; eexists. 

      Succeed solve [TacticsFW.in_compute_trace_inv_singleton_fw_solve 1 1]. 
Abort.

(* Not tested : rules with several output patterns *)

(* Not tested : iteration-count > 0 *) 

(* Not tested : guards that depend on the model *)
