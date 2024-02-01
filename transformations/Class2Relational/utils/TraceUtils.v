Require Import String.


Require Import Coq.Arith.EqNat.
Require Import List.

Open Scope string_scope.

Require Import core.utils.Utils.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

From usertools Require TacticsFW TacticsBW. 


Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From transformations.Class2Relational 
  Require C2RTactics.

Import PoorTraceLink.

(** Utilities on traces built by the Class2Relational transformation.
    In particular, all the results on [resolve], which appears in the code of the C2R transformation, rely on traces. *)





(* FW *)
(** We can statically know what each Class will yield in the poor trace: *)
Lemma class_in_trace c (cm : ClassModel) : 
  In (ClassElement c) cm.(modelElements) -> 
  In 
    (
       {| 
         source := ([ClassElement c],0,"tab")  ;
         produced := TableElement (C2RTactics.convert_class c)
       |}
    ) 
    (TraceLink.drop (compute_trace Class2Relational cm)).
Proof.
  intro IN1.

  apply TraceLink.in_drop_inv.

  eexists.
  simpl. 
  TacticsFW.in_compute_trace_inv_singleton_fw 1 1 IN1 ; reflexivity.
Qed.


(** Discrminating predicate to switch between [List.In] and [List.find]. 

We need to deal with List.find because it is used in the definition of Resolve.
*)

Lemma discr m:
  forall s : list ClassMetamodel.Element * nat * string,
    discriminating_predicate
      (fun x : TraceLink => source_compare s x = true)
      (TraceLink.drop (compute_trace Class2Relational m)).
Proof.
  intro s.
  intros a b IN1 IN2 C1 C2.
  destruct a.
  apply source_compare_correct in C1.
  simpl in C1.
  subst.
  destruct b.
  apply source_compare_correct in C2.
  simpl in C2.
  subst.
  f_equal.
  
  TacticsBW.exploit_in_trace IN1; 
  TacticsBW.exploit_in_trace IN2 ;
  reflexivity.
Qed.

Lemma in_find m : 
  forall c,
    In {|
         source :=  ([ClassElement c], 0, "tab") ;
         produced := TableElement (C2RTactics.convert_class c)
      |}
      (TraceLink.drop (compute_trace Class2Relational m)) ->
      find 
        (source_compare ([ClassElement c], 0, "tab"))
        (TraceLink.drop (compute_trace Class2Relational m)) = 
        Some 
          {|
            source := ([ClassElement c], 0, "tab") ;
            produced := TableElement (C2RTactics.convert_class c)
          |}.
Proof.

  intros c H.
  apply ListUtils.in_find.
  { apply discr. }
  {
    unfold source_compare ; simpl.
    unfold TransformationConfiguration.SourceElement_eqb.
    simpl.    
    rewrite Metamodel.beq_refl ; reflexivity.
  }

  { exact H. }

Qed.            
    
    
(* Resolve is a lookup in the trace. Resolve is called from the user defined transformation. *)
      
Local Lemma in_trace_resolve m c : 
  In {|
      source := ([ClassElement c], 0, "tab") ;
      produced := TableElement (C2RTactics.convert_class c)
    |} 
    (TraceLink.drop (compute_trace Class2Relational m)) ->
  Resolve.resolveIter (TraceLink.drop (compute_trace Class2Relational m)) "tab" [ClassElement c] 0 = 
    Some (TableElement (C2RTactics.convert_class c)).
Proof.
  unfold Resolve.resolveIter. 
  intros IN1.
  specialize (in_find _ c IN1) ; intro T5 ; clear IN1.
  unfold TransformationConfiguration.SourceElementType ; simpl.
  rewrite T5.
  simpl produced.
  reflexivity.
Qed.



Lemma in_model_resolve c (cm : ClassModel) :
  
  In (ClassElement c) cm.(modelElements) -> 
  
  Resolve.resolve (TraceLink.drop (compute_trace Class2Relational cm)) "tab" [ClassElement c]  =  
    Some (TableElement (C2RTactics.convert_class c)) 
  
  /\ In 
       (TableElement (C2RTactics.convert_class c)) 
       (execute Class2Relational cm).(modelElements).
Proof.
  intro H.
  unfold Resolve.resolve.
  apply class_in_trace in H.
  rewrite in_trace_resolve ; [ | exact H ].
  split ; [ reflexivity | ].
  destruct c.
  unfold C2RTactics.convert_class in *. simpl in *.
  unfold produced_elements.  
  apply in_map_iff.
  apply   TraceLink.in_drop_inv in H ; simpl in *.
  destruct H ; simpl in *.
  eexists ; split ; [ | eassumption] ; reflexivity.  
Qed.


