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

Ltac exploit_in_trace H :=
destruct (Tactics.destruct_in_trace_lem H) 
    as (se & r & i & e & te & IN_SOURCE & IN_RULE & MATCH_GUARD & IN_IT & IN_OUTPAT & EQ & EV);

  (* 2 *)
  Tactics.progress_in_In_rules IN_RULE ;

  (* _ *)
  Tactics.exploit_evalGuard MATCH_GUARD  ; 

  (* _ *)
  Tactics.exploit_in_it IN_IT ;

  (* 3 *)
  Tactics.progress_in_In_outpat IN_OUTPAT ;

  (* 5 *) 
  Tactics.exploit_evaloutpat EV ; 

  (* (7) *)
  (* not useful here *)
  Semantics.in_allTuples_auto.



Definition convert_class c :=
  {| Table_id := c.(Class_id); Table_name := c.(Class_name)  |}.


Lemma trace_class m :
  forall c t,
  In (buildTraceLink 
        ([ClassElement c], 0, "tab")
        (TableElement t))
    (RichTraceLink.drop (traceTrOnModel Class2Relational m)) ->
  t = convert_class c.
Proof.  
  intros c t H.

  exploit_in_trace H.
  PropUtils.inj EQ.
  reflexivity.
Qed.

Definition convert_attribute c :=
  {| Column_id := c.(Attribute_id); Column_name := c.(Attribute_name)  |}.


Lemma trace_attribute m :
  forall a c,
  In (buildTraceLink 
        ([AttributeElement a], 0, "col")
        (ColumnElement c))
    (RichTraceLink.drop (traceTrOnModel Class2Relational m)) ->
  c = convert_attribute a.
Proof.  
  intros c t H.

  exploit_in_trace H.
  PropUtils.inj EQ.
  reflexivity.
Qed.

Lemma in_trace_inv m t :
In t (RichTraceLink.drop (traceTrOnModel Class2Relational m)) ->
   (exists a, t = (buildTraceLink 
        ([AttributeElement a], 0, "col")
        (ColumnElement (convert_attribute a)))) \/ (exists c, t = buildTraceLink 
        ([ClassElement c], 0, "tab")
        (TableElement (convert_class c))).
Proof.
  intro H.
  exploit_in_trace H.
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




(** Local lemma. *)
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
  {
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
    destruct (in_trace_inv _ _ IN1) ; [ exfalso | ].
    { destruct H0 ; discriminate. }
    destruct (in_trace_inv _ _ IN2) ; [ exfalso | ].
    { destruct H1 ; discriminate. }
    destruct H0 as (? & E1) ; PropUtils.inj E1.
    destruct H1 as (? & E2) ; PropUtils.inj E2.
    reflexivity.
  }
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
        (TableElement (convert_class c))) (RichTraceLink.drop (traceTrOnModel Class2Relational m)) ->
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



Lemma in_trace c (cm : ClassModel) : 
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


Lemma in_maybeResolve_trace_2 c (cm : ClassModel) :
  
  In (ClassElement c) cm.(modelElements) -> 
  
  Resolve.maybeResolve (RichTraceLink.drop (traceTrOnModel Class2Relational cm)) "tab" (Some [ClassElement c])  =  
    Some (TableElement (convert_class c)) 
  
  /\ In 
       (TableElement (convert_class c)) 
       (execute Class2Relational cm).(modelElements).
Proof.
  intro H.
  unfold Resolve.maybeResolve.
  unfold Resolve.resolve.
  apply in_trace in H.
  rewrite in_resolve ; [ | exact H ].
  split ; [ reflexivity | ].
  eapply Tactics.in_trace_in_models_target in H ; eauto. 
Qed.

