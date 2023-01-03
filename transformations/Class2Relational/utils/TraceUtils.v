Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.

Require Import core.utils.Utils.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From transformations.Class2Relational Require Tactics.


(** Utilities on traces *)

Inductive CoherentTrace : TraceLink.TraceLink -> Prop :=

 | ct_class :
   forall t,
     CoherentTrace 
       (TraceLink.buildTraceLink 
          ([ClassElement t], 0, "tab"%string)
          (TableElement
             {|
               table_id := class_id t; 
               table_name := class_name t
             |}))

 | ct_attribute :
   forall a,
     CoherentTrace
       (TraceLink.buildTraceLink 
          ([AttributeElement a], 0, "col"%string)
          (ColumnElement
             {|
               column_id := attr_id a ;
               column_name :=  attr_name a 
             |})).

Lemma trace_wf cm :
  Forall CoherentTrace (trace Class2Relational cm).
Proof.
  unfold trace.
  unfold allTuples.
  apply Forall_flat_map.
  simpl.
  unfold prod_cons.
  apply Forall_forall.
  intro l.
  intro H.
  apply Forall_flat_map.
  apply Forall_forall.
  intro r.
  intro H2.
  apply in_app_or in H.
  destruct_or H.
  2:{ simpl in *.
      remove_or_false H.
      subst l.
      simpl in *.
      contradiction.
  }
  apply in_flat_map in H.
  destruct H as (e & H3 & H4).
  simpl in *.
  remove_or_false H4.
  subst l.
  simpl in *.
  unfold matchPattern in H2.
  apply filter_In in H2.
  destruct H2 as [H4 H5].

  
  Tactics.destruct_In_two ; simpl in * ; Tactics.deduce_element_kind_from_guard.
  { repeat constructor. }  
  { repeat constructor. }  
Qed.



Lemma in_find_5bis l : 
  Forall CoherentTrace l ->
  forall t,
    In (TraceLink.buildTraceLink
          ([ClassElement t], 0, "tab"%string)
          (TableElement {| table_id := class_id t; table_name := class_name t |})) l ->
    exists r1 , 
      find
        (fun tl : TraceLink.TraceLink =>
           (Semantics.list_beq
              (Metamodel.ElementType
                 TransformationConfiguration.SourceMetamodel)
              TransformationConfiguration.SourceElement_eqb
              (TraceLink.TraceLink_getSourcePattern tl)
              (singleton (ClassElement t)) &&
              (TraceLink.TraceLink_getIterator tl =? 0) &&
              (TraceLink.TraceLink_getName tl =? "tab")%string)%bool) l = 
        Some (TraceLink.buildTraceLink r1 (TableElement {| table_id := class_id t; table_name := class_name t |})).
Proof.
  induction l ; intros C t IN1 ; [ simpl in IN1 ; contradict IN1 | ].
  simpl.
  apply in_inv in IN1. 
  compare a (TraceLink.buildTraceLink ([ClassElement t], 0, "tab"%string)
          (TableElement
             {| table_id := class_id t; table_name := class_name t |})). 


  { (* case where the class/table is the first element of the list : no induction *)
    clear IN1 ; intro ; subst a.
    simpl.
    unfold TransformationConfiguration.SourceElement_eqb .
    unfold Metamodel.elements_eqdec.
    unfold TransformationConfiguration.SourceMetamodel.
    unfold C2RConfiguration. simpl.
    rewrite beq_Class_refl. simpl.
    eauto.
  }           
  
  { (* case where the class/table is not the first element of the list. *)
    intro D.
    inversion_clear C ; subst.
    
    inversion_clear H.
    { (* class/table *)
      destruct_or IN1 ; [ contradict D ; assumption | ].

      destruct (IHl H0 t) ; [  exact IN1 | ].
      unfold TransformationConfiguration.SourceElement_eqb .
      unfold Metamodel.elements_eqdec.
      unfold TransformationConfiguration.SourceMetamodel.
      unfold C2RConfiguration. simpl.
      repeat rewrite Bool.andb_true_r.
      destruct (beq_Class t0 t) eqn:BEQ.
      {  apply lem_beq_Class_id in BEQ ; subst ; eauto.  }
      {
        simpl in H.

        unfold TransformationConfiguration.SourceElement_eqb in H.
        unfold Metamodel.elements_eqdec.
        
        match goal with 
          [ H : find ?X ?Y = ?Z |- context [find ?A ?B] ] => 
            replace (find A B) with Z end.
        { eauto. }
      }
    }       
    { (* attribute/column*)
      destruct_or IN1.
      { contradict IN1. exact D. }
      destruct (IHl H0 t) ; [  exact IN1 | ].
      unfold TransformationConfiguration.SourceElement_eqb .
      unfold Metamodel.elements_eqdec.
      unfold TransformationConfiguration.SourceMetamodel.
      unfold C2RConfiguration. simpl. 
      exists x.
      apply H.
    }
  }
  { repeat decide equality. }
  { repeat decide equality. }

Qed.            
        

      
Lemma in_resolve_4bis  l t cm : 
  Forall CoherentTrace l ->
  In (TraceLink.buildTraceLink
        ([ClassElement t], 0, "tab"%string)
        (TableElement
           {| table_id := class_id t; table_name := class_name t |})) l ->
  resolveIter l cm "tab"
    (singleton (ClassElement t)) 0 = Some (TableElement {| table_id := class_id t; table_name := class_name t |}).
Proof.
  unfold resolveIter. 
  intros C IN1.
  specialize (in_find_5bis l C t IN1) ; intro T5 ; clear IN1.
  
  destruct T5 as (t1 & IN1).
  rewrite IN1.
  unfold TraceLink.TraceLink_getTargetElement.
  destruct t1.
  destruct p.
  reflexivity.
Qed.

Lemma in_trace_3  e (cm : ClassModel) : 
  In (ClassElement e) cm.(modelElements) -> 
  In 
    (TraceLink.buildTraceLink ([ClassElement e],0,"tab"%string) (TableElement {| table_id := class_id e; table_name := class_name e |})) 
    (trace Class2Relational cm).
Proof.
  intro IN1.
  unfold trace.
  apply in_flat_map.
  exists ([ClassElement e]).
  split.
  { apply Tactics.allModelElements_allTuples ; auto. } 
  { compute. left. reflexivity. }
Qed.
