Require Import  TestUtils.

Require ConcreteExpressionTools Semantics.

Import 
  List Model String NotationUtils Semantics PoorTraceLink  NotationUtils.

Open Scope string_scope.

Require Class2Relational.Class2Relational.


Section TestInvMakeLink.

(* Tactic under test : [ConcreteExpressionTools.inv_makeLink] *)
(* Test case : *)

  Import ClassMetamodel RelationalMetamodel Class2Relational.
  Import Glue.
  
  Context 
    (cm : ClassModel) 
    (a : Attribute_t)

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
             (TraceLink.drop (Semantics.compute_trace Class2Relational cm)) 
             0 
             cm
             [AttributeElement a]
             (ColumnElement
                {|
                  Column_id := Attribute_id a;
                  Column_name := Attribute_name a
                |}) = return l).
  
  Goal 
    exists a_type, 
      getAttribute_typeElement a cm = return a_type  
      /\ exists res,
        ModelingSemantics.resolve
          (TraceLink.drop (compute_trace Class2Relational cm)) "tab"
          Table_K (ListUtils.singleton a_type) = return res
        /\      l = [Column_referenceLink
                       (glue {|
                            Column_id := Attribute_id a;
                            Column_name := Attribute_name a
                          |} with res)]
  .
  
  Proof. 
    tested_tactic "ConcreteExpressionTools.inv_makeLink.".
    test_case "Typical use (Class2Relational).".

    tryif 
      ConcreteExpressionTools.inv_makeLink H ;
      unfold get_E_data in EQ ;
    injection EQ ; clear EQ ; intro EQ ; subst ;
      eexists ;
      split ; [ | eexists ; split] ; [ reflexivity | eassumption | reflexivity ]
      
    then test_success
    else test_failure.

  Abort.  
  
End TestInvMakeLink.


Section TestInvMakeLink2.

(* Tactic under test : [ConcreteExpressionTools.inv_makeLink] *)

  Import ClassMetamodel RelationalMetamodel Class2Relational.
  Import Glue.
  
  Context 
    (cm : ClassModel) 
    (a : Attribute_t)
  
    (l : list RelationalMetamodel.Link)
    (lk: RelationalMetamodel.Column_reference_glue)
    (tr:Trace)  

    (H : ConcreteExpressions.makeLink 
          [Attribute_K] 
          Column_K
          Column_reference_K
          (fun _ _ _ _ _ => return lk)
          tr  
          0
          cm
          [AttributeElement a]
          (ColumnElement
                {|
                  Column_id := Attribute_id a;
                  Column_name := Attribute_name a
                |}
          )
        = return l).
  
  Goal 
   l=[Column_referenceLink lk].

  
  Proof. 
    tested_tactic "ConcreteExpressionTools.inv_makeLink.".
    test_case "Typical use (Identity transformation).".

  tryif
    ConcreteExpressionTools.inv_makeLink H ; reflexivity
  then test_success
  else test_failure. 

  Abort.  
  
End TestInvMakeLink2.


Section TestWrapInv.

(* Tactic under test : [ConcreteExpressionTools.wrap_inv] *)

  Import ClassMetamodel RelationalMetamodel Class2Relational.
  Import Glue.

Context
 (cm : ClassModel)
 (i : nat)
 (n : string)
 (t : Class_t)
 (IN_ELTS : incl [ClassElement t] (modelElements cm))
 (H : ConcreteExpressions.wrap [Class_K]
       (fun c : Class_t =>
        return {| Table_id := Class_id c; Table_name := Class_name c |})
       [ClassElement t] =
     return (return {| Table_id := i; Table_name := n |})).

Goal False. 

Proof.
    tested_tactic "ConcreteExpressionTools.wrap_inv.".
    test_case "Typical use.".

 tryif
   ConcreteExpressionTools.wrap_inv H
 then test_success
 else test_failure.  

Abort.

End TestWrapInv.
