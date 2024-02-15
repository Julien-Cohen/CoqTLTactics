Require Import  TestUtils.

Require ConcreteExpressionTools Semantics.

Import 
  List Model String NotationUtils Semantics PoorTraceLink  NotationUtils.

Open Scope string_scope.

Require Class2Relational.Class2Relational.

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
             (TraceLink.drop (Semantics.compute_trace Class2Relational cm)) 0 cm
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
