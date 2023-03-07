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

Import TraceLink.

(** * Utilities on traces built by the Class2Relational transformation. *)


Inductive CoherentTraceLink : TraceLink -> Prop :=

 | ct_class :
   forall (c:Class_t),
     CoherentTraceLink 
       (buildTraceLink 
          ([ClassElement c], 0, "tab")
          (TableElement
             {|
               table_id := c.(class_id); 
               table_name := c.(class_name) 
             |}))

 | ct_attribute :
   forall (a:Attribute_t),
     CoherentTraceLink
       (buildTraceLink 
          ([AttributeElement a], 0, "col")
          (ColumnElement
             {|
               column_id := a.(attr_id) ;
               column_name :=  a.(attr_name) 
             |})).


Definition wf t : Prop := 
  List.Forall CoherentTraceLink t.


(** Traces built by the Class2Relational transformation are well-formed. *)


Lemma trace_wf cm :
  wf (trace Class2Relational cm).
Proof.
  unfold wf.
  apply Forall_forall.
  intros l H.  

  (* (1) *)
  destruct (Tactics.destruct_in_trace_lem H) 
    as (se & r & i & e & te & IN_SOURCE & IN_RULE & MATCH_GUARD & IN_IT & IN_OUTPAT & EQ & EV) ; subst l.

  (* 2 *)
  Tactics.progress_in_In_rules IN_RULE ;

  (* 3 *)
  Tactics.progress_in_ope IN_OUTPAT ;

  (* 4 *)
  Tactics.exploit_evalGuard MATCH_GUARD  ; 

  (* 5 *) 
  Tactics.exploit_evaloutpat EV ; 

  (* 6 *)
  Tactics.exploit_in_it IN_IT ;

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
          (TableElement {| table_id := c.(class_id); 
                          table_name := c.(class_name)  |})) t ->
    exists r1 , 
      find (source_compare ([ClassElement c], 0, "tab")) t = 
        Some 
          (buildTraceLink r1 
             (TableElement {| table_id := c.(class_id); 
                             table_name := c.(class_name) |})).
Proof.
  induction t ; intros WF c IN1 ; [ simpl in IN1 ; contradict IN1 | ].
  simpl find.
  apply in_inv in IN1. 
  (* destruct or IN1 does not help here because in the "right" case we need to know that the "left" case is false. *) 

  compare a (buildTraceLink ([ClassElement c], 0, "tab")
          (TableElement
             {| table_id := c.(class_id); table_name := c.(class_name) |})). 


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
        apply beq_Class_refl. 
        apply beq_Attribute_refl.
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
      destruct (beq_Class c0 c) eqn:BEQ.
      {  apply lem_beq_Class_id in BEQ ; subst ; eauto.  }
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
        

      
Lemma in_resolve t c cm : 
  wf t ->
  In (buildTraceLink
        ([ClassElement c], 0, "tab")
        (TableElement
           {| table_id := c.(class_id); table_name := c.(class_name) |})) t ->
  resolveIter t cm "tab" [ClassElement c] 0 = 
    Some (TableElement {| table_id := c.(class_id); table_name := c.(class_name) |}).
Proof.
  unfold resolveIter. 
  intros C IN1.
  specialize (in_find t C c IN1) ; intro T5 ; clear IN1.
  destruct T5 as (t1 & IN1).
  (* Set Printing All. *)
  unfold TransformationConfiguration.SourceElementType ; simpl.
  rewrite IN1.
  simpl target.
  reflexivity.
Qed.



Lemma in_trace c (cm : ClassModel) : 
  In (ClassElement c) cm.(modelElements) -> 
  In 
    (buildTraceLink 
       ([ClassElement c],0,"tab") 
       (TableElement 
          {| 
            table_id := c.(class_id); 
            table_name := c.(class_name) 
          |}
         )
    ) 
    (trace Class2Relational cm).
Proof.
  intro IN1.

  Tactics.destruct_in_trace_G.

  exists ([ClassElement c]).
  split.
  { apply C2RTactics.allModelElements_allTuples ; auto. } 
  { compute. left. reflexivity. }
Qed.


Lemma in_maybeResolve_trace_2 c (cm : ClassModel) :
  
  In (ClassElement c) cm.(modelElements) -> 
  
  maybeResolve (trace Class2Relational cm) cm "tab" (Some [ClassElement c])  =  
    Some (TableElement {| table_id := c.(class_id); table_name := c.(class_name) |}) 
  
  /\ In 
       (TableElement {| table_id := c.(class_id); table_name := c.(class_name) |}) 
       (execute Class2Relational cm).(modelElements).
Proof.
  intro H.
  unfold maybeResolve.
  unfold resolve.
  apply in_trace in H.
  rewrite in_resolve ; [ | solve [apply trace_wf] | exact H ].
  split ; [ reflexivity | ].
  eapply Tactics.in_trace_in_models_target in H ; eauto. 
Qed.

