Require Import String.


Require Import Coq.Arith.EqNat.
Require Import List.

Open Scope string_scope.

Require Import core.utils.Utils.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From transformations.Class2Relational 
  Require C2RTactics.

Import PoorTraceLink.

(** * Utilities on traces built by the Class2Relational transformation. *)


Definition convert_class c :=
  {| Table_id := c.(Class_id) ; Table_name := c.(Class_name) |}.

Definition convert_attribute c :=
  {| Column_id := c.(Attribute_id) ; Column_name := c.(Attribute_name) |}.

Lemma in_trace_inv m t :
  In t (RichTraceLink.drop (traceTrOnModel Class2Relational m)) ->
  
  (exists a, t = (buildTraceLink 
        ([AttributeElement a], 0, "col")
        (ColumnElement (convert_attribute a))))
   \/ 
   (exists c, t = buildTraceLink 
        ([ClassElement c], 0, "tab")
        (TableElement (convert_class c))).
Proof.
  intro H.
  Tactics.exploit_in_trace H.
  { right. simpl in *.
    eexists. 
    f_equal.
    reflexivity.
  }
  { left. simpl in *.
    eexists.
    f_equal.
    reflexivity.
  }
Qed.



Lemma class_in_trace c (cm : ClassModel) : 
  In (ClassElement c) cm.(modelElements) -> 
  In 
    (buildTraceLink 
       ([ClassElement c],0,"tab") 
       (TableElement (convert_class c))
    ) 
    (RichTraceLink.drop (traceTrOnModel Class2Relational cm)).
Proof.
  intro IN1.

  unfold RichTraceLink.drop.
  apply in_map_iff.

  eexists.
  split.

  
  2:{
    Tactics.destruct_in_trace_G.
    
    exists ([ClassElement c]).
    split.
    { apply C2RTactics.allModelElements_allTuples ; auto. } 
    { compute. left. reflexivity. }
  }
  { reflexivity. }
Qed.


Lemma discr m:
  forall s : list ClassMetamodel.Element * nat * string,
    discriminating_predicate
      (fun x : TraceLink => source_compare s x = true)
      (RichTraceLink.drop (traceTrOnModel Class2Relational m)).
Proof.
  intro s.
  intros a b IN1 IN2 C1 C2.
  destruct a.
  apply source_compare_correct in C1.
  simpl in C1.
  subst.
  2:{
    simpl. apply ClassMetamodel.internal_Element_dec_bl.
  }    
  destruct b.
  apply source_compare_correct in C2.
  simpl in C2.
  subst.
  2:{
    apply ClassMetamodel.internal_Element_dec_bl.
  }    
  f_equal.
  
  Tactics.exploit_in_trace IN1; 
  Tactics.exploit_in_trace IN2 ;
  PropUtils.inj EQ0 ;
  PropUtils.inj EQ ; auto.
  discriminate.
  discriminate.
Qed.

Lemma in_find m : 
  forall c,
    In (buildTraceLink
          ([ClassElement c], 0, "tab")
          (TableElement (convert_class c))) (RichTraceLink.drop (traceTrOnModel Class2Relational m)) ->
      find (source_compare ([ClassElement c], 0, "tab")) (RichTraceLink.drop (traceTrOnModel Class2Relational m)) = 
        Some 
          (buildTraceLink ([ClassElement c], 0, "tab") 
             (TableElement (convert_class c))).
Proof.

  intros c H.
  apply ListUtils.in_find.
  { apply discr. }
  {
    unfold source_compare ; simpl.
    unfold TransformationConfiguration.SourceElement_eqb.
    simpl.    
    rewrite internal_Class_t_dec_lb ; reflexivity.
  }

  { exact H. }

Qed.            
        

      
Lemma in_resolve m c : 
  In (buildTraceLink
        ([ClassElement c], 0, "tab")
        (TableElement (convert_class c))) 
    (RichTraceLink.drop (traceTrOnModel Class2Relational m)) ->
  Resolve.resolveIter (RichTraceLink.drop (traceTrOnModel Class2Relational m)) "tab" [ClassElement c] 0 = 
    Some (TableElement (convert_class c)).
Proof.
  unfold Resolve.resolveIter. 
  intros IN1.
  specialize (in_find _ c IN1) ; intro T5 ; clear IN1.
  unfold TransformationConfiguration.SourceElementType ; simpl.
  rewrite T5.
  simpl produced.
  reflexivity.
Qed.



Lemma in_Resolve_trace_2 c (cm : ClassModel) :
  
  In (ClassElement c) cm.(modelElements) -> 
  
  Resolve.resolve (RichTraceLink.drop (traceTrOnModel Class2Relational cm)) "tab" [ClassElement c]  =  
    Some (TableElement (convert_class c)) 
  
  /\ In 
       (TableElement (convert_class c)) 
       (execute Class2Relational cm).(modelElements).
Proof.
  intro H.
  unfold Resolve.resolve.
  apply class_in_trace in H.
  rewrite in_resolve ; [ | exact H ].
  split ; [ reflexivity | ].
  eapply Tactics.in_trace_in_models_target in H ; eauto. 
Qed.


(* FIXME : remove-me *)
Corollary in_maybeResolve_trace_2 c (cm : ClassModel) :
  
  In (ClassElement c) cm.(modelElements) -> 
  
  Resolve.maybeResolve (RichTraceLink.drop (traceTrOnModel Class2Relational cm)) "tab" (Some [ClassElement c])  =  
    Some (TableElement (convert_class c)) 
  
  /\ In 
       (TableElement (convert_class c)) 
       (execute Class2Relational cm).(modelElements).
Proof.
  unfold Resolve.maybeResolve.
  apply in_Resolve_trace_2. 
Qed.


