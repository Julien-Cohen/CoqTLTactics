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


Inductive CoherentTraceLink : TraceLink -> Prop :=

 | ct_class :
   forall (c:Class_t),
     CoherentTraceLink 
       (buildTraceLink 
          ([ClassElement c], 0, "tab")
          (TableElement
             {|
               table_id := c.(Class_id); 
               table_name := c.(Class_name) 
             |}))

 | ct_attribute :
   forall (a:Attribute_t),
     CoherentTraceLink
       (buildTraceLink 
          ([AttributeElement a], 0, "col")
          (ColumnElement
             {|
               column_id := a.(Attribute_id) ;
               column_name :=  a.(Attribute_name) 
             |})).


Definition wf t : Prop := 
  List.Forall CoherentTraceLink t.


(** Traces built by the Class2Relational transformation are well-formed. *)


Lemma trace_wf :
  forall cm, wf (RichTraceLink.convert2 (traceTrOnModel Class2Relational cm)).
Proof.
  intro cm. 
  unfold wf.
  apply Forall_forall.
  intros l H.  

  (* (1) *)
  destruct (Tactics.destruct_in_trace_lem H) 
    as (se & r & i & e & te & IN_SOURCE & IN_RULE & MATCH_GUARD & IN_IT & IN_OUTPAT & EQ & EV) ; subst l.

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

  { (* rule 1 *) 
    constructor 1. 
  }  
  { (* rule 2 *)
    constructor 2.
  }  
Qed.





(** Local lemma. *)
Lemma in_find t : 
  wf t ->
  forall c,
    In (buildTraceLink
          ([ClassElement c], 0, "tab")
          (TableElement {| table_id := c.(Class_id); 
                          table_name := c.(Class_name)  |})) t ->
    exists r1 , 
      find (source_compare ([ClassElement c], 0, "tab")) t = 
        Some 
          (buildTraceLink r1 
             (TableElement {| table_id := c.(Class_id); 
                             table_name := c.(Class_name) |})).
Proof.
  induction t ; intros WF c IN1 ; [ simpl in IN1 ; contradict IN1 | ].
  simpl find.
  apply in_inv in IN1. 
  (* destruct or IN1 does not help here because in the "right" case we need to know that the "left" case is false. *) 

  compare a (buildTraceLink ([ClassElement c], 0, "tab")
          (TableElement
             {| table_id := c.(Class_id); table_name := c.(Class_name) |})). 


  { (* case where the class/table is the first element of the list : no induction *)
    clear IN1 ; intro ; subst a.
    rewrite source_compare_refl.
    { solve [eauto]. }
    { 
      unfold TransformationConfiguration.SourceElement_eqb ; simpl.
      { (* reflexivity *)
        (* FIXME : add reflexivity as a constraint in Metamodels *)
        clear.
        destruct a.
        apply lem_Class_t_beq_refl. 
        apply lem_Attribute_t_beq_refl.
      }           
    }
  }  
  { (* case where the class/table is not the first element of the list. *)
    intro D.
    destruct_or IN1 ; [ contradict D ; assumption | ].

    inversion_clear WF.
    destruct (IHt H0 c) ; [  exact IN1 | ].

    inversion_clear H.
    { (* class/table *)
      
      unfold source_compare at 1 ; simpl.
      unfold TransformationConfiguration.SourceElement_eqb ; simpl.

      repeat rewrite Bool.andb_true_r.
      destruct (Class_t_beq c0 c) eqn:BEQ.
      {  apply lem_Class_t_beq_id in BEQ ; subst ; eauto.  }
      {
        rewrite H1.
        eauto. 
      }
    }       
    { (* attribute/column*)
      simpl.
      rewrite H1.
      eauto.
    }
  }
  { repeat decide equality. }
  { repeat decide equality. }

Qed.            
        

      
Lemma in_resolve t c : 
  wf t ->
  In (buildTraceLink
        ([ClassElement c], 0, "tab")
        (TableElement
           {| table_id := c.(Class_id); table_name := c.(Class_name) |})) t ->
  Resolve.resolveIter t "tab" [ClassElement c] 0 = 
    Some (TableElement {| table_id := c.(Class_id); table_name := c.(Class_name) |}).
Proof.
  unfold Resolve.resolveIter. 
  intros C IN1.
  specialize (in_find t C c IN1) ; intro T5 ; clear IN1.
  destruct T5 as (t1 & IN1).
  (* Set Printing All. *)
  unfold TransformationConfiguration.SourceElementType ; simpl.
  rewrite IN1.
  simpl produced.
  reflexivity.
Qed.



Lemma in_trace c (cm : ClassModel) : 
  In (ClassElement c) cm.(modelElements) -> 
  In 
    (buildTraceLink 
       ([ClassElement c],0,"tab") 
       (TableElement 
          {| 
            table_id := c.(Class_id); 
            table_name := c.(Class_name) 
          |}
         )
    ) 
    (RichTraceLink.convert2 (traceTrOnModel Class2Relational cm)).
Proof.
  intro IN1.

  unfold RichTraceLink.convert2.
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
  
  Resolve.maybeResolve (RichTraceLink.convert2 (traceTrOnModel Class2Relational cm)) "tab" (Some [ClassElement c])  =  
    Some (TableElement {| table_id := c.(Class_id); table_name := c.(Class_name) |}) 
  
  /\ In 
       (TableElement {| table_id := c.(Class_id); table_name := c.(Class_name) |}) 
       (execute Class2Relational cm).(modelElements).
Proof.
  intro H.
  unfold Resolve.maybeResolve.
  unfold Resolve.resolve.
  apply in_trace in H.
  rewrite in_resolve ; [ | solve [apply trace_wf] | exact H ].
  split ; [ reflexivity | ].
  eapply Tactics.in_trace_in_models_target in H ; eauto. 
Qed.

