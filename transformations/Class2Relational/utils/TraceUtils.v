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


Lemma in_find_5bis t : 
  wf t ->
  forall c,
    In (buildTraceLink
          ([ClassElement c], 0, "tab")
          (TableElement {| table_id := c.(class_id); table_name := c.(class_name)  |})) t ->
    exists r1 , 
      find (source_compare ([ClassElement c], 0, "tab")) t = 
        Some (buildTraceLink r1 (TableElement {| table_id := c.(class_id); table_name := c.(class_name) |})).
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
    solve [eauto].
    unfold TransformationConfiguration.SourceElement_eqb ; simpl.
    { (* reflexivity *)
      (* FIXME : add reflexivity as a constraint in Metamodels *)
      clear.
      destruct a.
      apply beq_Class_refl. 
      apply beq_Attribute_refl.
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
        

      
Lemma in_resolve_4bis t c cm : 
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
  specialize (in_find_5bis t C c IN1) ; intro T5 ; clear IN1.
  destruct T5 as (t1 & IN1).
  (* Set Printing All. *)
  unfold TransformationConfiguration.SourceElementType ; simpl.
  rewrite IN1.
  simpl target.
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
