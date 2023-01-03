Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.
Require Import Coq.Arith.Gt.
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

From transformations.Class2Relational Require Tactics.

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
  unfold trace.
  unfold allTuples.
  unfold wf.
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

  (* remove [nil] in H (l cannot be nil)*)
  apply in_app_or in H.
  destruct_or H.
  2:{ 
    apply ListUtils.in_singleton in H ; subst l. 
    simpl in *. contradiction.
  }
  (* done *)

  apply in_flat_map in H.
  destruct H as (e & H3 & H4).
  simpl map in H4.
  apply ListUtils.in_singleton in H4 ; subst l.

  unfold matchPattern in H2.
  apply filter_In in H2.
  destruct H2 as [H4 H5].

  
  Tactics.destruct_In_two ; simpl in * ; Tactics.deduce_element_kind_from_guard.
  { (* rule 1 *) compute. constructor. constructor. constructor. }  
  { (* rule 2 *) compute. constructor. constructor. constructor. }  
Qed.


Notation match_source s  :=
  (fun (t:TraceLink) => 
     match s with (e,i,n) =>
                    ((Semantics.list_beq _
                        TransformationConfiguration.SourceElement_eqb
                        (TraceLink_getSourcePattern t)
                        e) 
                     && beq_nat (TraceLink_getIterator t) i
                     && String.eqb (TraceLink_getName t) n)%bool
     end).

Lemma in_find_5bis t : 
  wf t ->
  forall c,
    In (buildTraceLink
          ([ClassElement c], 0, "tab")
          (TableElement {| table_id := c.(class_id); table_name := c.(class_name)  |})) t ->
    exists r1 , 
      find (match_source ([ClassElement c], 0, "tab")) t = 
        Some (buildTraceLink r1 (TableElement {| table_id := c.(class_id); table_name := c.(class_name) |})).
Proof.
  induction t ; intros C c IN1 ; [ simpl in IN1 ; contradict IN1 | ].
  simpl.
  apply in_inv in IN1. 
  compare a (buildTraceLink ([ClassElement c], 0, "tab")
          (TableElement
             {| table_id := c.(class_id); table_name := c.(class_name) |})). 


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

      destruct (IHt H0 c) ; [  exact IN1 | ].
      unfold TransformationConfiguration.SourceElement_eqb .
      unfold Metamodel.elements_eqdec.
      unfold TransformationConfiguration.SourceMetamodel.
      unfold C2RConfiguration. simpl.
      repeat rewrite Bool.andb_true_r.
      destruct (beq_Class c0 c) eqn:BEQ.
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
      destruct (IHt H0 c) ; [  exact IN1 | ].
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
        

      
Lemma in_resolve_4bis t c cm : 
  wf t ->
  In (buildTraceLink
        ([ClassElement c], 0, "tab")
        (TableElement
           {| table_id := c.(class_id); table_name := c.(class_name) |})) t ->
  resolveIter t cm "tab" (singleton (ClassElement c)) 0 = 
    Some (TableElement {| table_id := c.(class_id); table_name := c.(class_name) |}).
Proof.
  unfold resolveIter. 
  (* FIXME : in resolveIter, introduce match_source *)
  intros C IN1.
  specialize (in_find_5bis t C c IN1) ; intro T5 ; clear IN1.
  destruct T5 as (t1 & IN1).
  unfold singleton.
  rewrite IN1.
  unfold TraceLink_getTargetElement.
  destruct t1.
  destruct p.
  reflexivity.
Qed.

Lemma in_trace_3 c (cm : ClassModel) : 
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
  unfold trace.
  apply in_flat_map.
  exists ([ClassElement c]).
  split.
  { apply Tactics.allModelElements_allTuples ; auto. } 
  { compute. left. reflexivity. }
Qed.
