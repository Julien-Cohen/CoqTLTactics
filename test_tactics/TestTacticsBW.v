Require Import  TestUtils.


Require TacticsBW.


Import 
  List Model String NotationUtils Semantics PoorTraceLink  NotationUtils Semantics.


Open Scope string_scope.

Require Class2Relational.Class2Relational.


(** Tests for tactics on elements. *)

Section Test1.

(* Tactic under test : [TacticsBW.exploit_element_in_result] *)
(* Test case : *)

  Import ClassMetamodel RelationalMetamodel Class2Relational.

  Context 
    (cm : ClassModel) (i : nat) (n : string).
  
  Goal
    forall (H : In 
                  (TableElement 
                     {|
                       Table_id := i;
                       Table_name := n 
                     |})
                  (modelElements (execute Class2Relational cm))),
    exists c, 
      In (ClassElement c) (modelElements cm) 
      /\ c.(Class_id) = i 
      /\ c.(Class_name) = n.
  
  Proof.
    idtac "Testing TacticsBW.exploit_element_in_result".
    idtac "Test case : ".

    intros.    

    tryif 
      TacticsBW.exploit_element_in_result H ; [] ;
      solve [eauto]
    then test_success
    else test_failure.
    
  Abort.
  
End Test1.


(** Tests for tactics on links. *)

Section TestOther1.

(* Tactic under test : [ConcreteExpressionTools.inv_makeLink] *)
(* Test case : *)

  Import ClassMetamodel RelationalMetamodel Class2Relational.
  Import Glue.
  
  Context 
    (cm : ClassModel) 
      (t : Attribute_t)
      (l : list RelationalMetamodel.Link)
      (H : ConcreteExpressions.makeLink [Attribute_K] Column_K
             Column_reference_K
             (fun (thisModule : Trace) (_ : nat)
                  (m : TransformationConfiguration.SourceModel)
                  (a : Attribute_t)
                  (c : Column_t) =>
                a_type <- getAttribute_typeElement a m;
              res <-
                ModelingSemantics.resolve thisModule "tab" Table_K
                  (ListUtils.singleton a_type); do_glue c with res)
             (TraceLink.drop (compute_trace Class2Relational cm)) 0 cm
             [AttributeElement t]
             (ColumnElement
                {|
                  Column_id := Attribute_id t;
                  Column_name := Attribute_name t
                |}) = return l).
  
  Goal False.
  
  Proof. 
    idtac "Testing ConcreteExpressionTools.inv_makeLink.".
    idtac "Test case : ".
    
    tryif 
      ConcreteExpressionTools.inv_makeLink H
    then test_success
    else test_failure.
    
  Abort.  
  
End TestOther1.


Section TestLink1.

(* Tactic under test : [TacticsBW.exploit_link_in_result] *)
(* Test case : *)

  Import ClassMetamodel RelationalMetamodel Class2Relational.
  Import Glue.
  
  Context
    (cm : ClassModel) (c : Column_t) (tb : Table_t).

Goal forall
      (R_IN1 : In (Column_referenceLink (glue c with tb))
                 (modelLinks (execute Class2Relational cm))),

     (* We expect to find the following in the hypothesis *)
    exists t e, 
      In (AttributeElement t) (modelElements cm) 
      /\  negb (Attribute_derived t) = true 
      /\ getAttribute_typeElement t cm = return e
      /\ ModelingSemantics.resolve
           (TraceLink.drop (compute_trace Class2Relational cm)) "tab"
           Table_K (ListUtils.singleton e) = return tb /\ 
        c = {| Column_id := t.(Attribute_id) ; Column_name := t.(Attribute_name) |}.
  
  Proof.
    idtac "Testing TacticsBW.exploit_link_in_result".
    idtac "Test case : ".

    intros. 
    

    tryif 
      TacticsBW.exploit_link_in_result R_IN1 ; [] ;
      eexists ; eexists ; split ; [ | split ; [ | split ; [ | split]]] ;
      [ eassumption | eassumption | eassumption | eassumption | unfold RelationalMetamodel.get_E_data in EQ ; congruence ]
    then test_success
    else test_failure.
    
  Abort.
  

End TestLink1.
