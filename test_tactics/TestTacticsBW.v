Require Import  TestUtils.


Require TacticsBW.


Import 
  List Model String NotationUtils Semantics PoorTraceLink  NotationUtils Semantics.


Open Scope string_scope.

Require Class2Relational.Class2Relational.

Section Test1.

(* Tactic under test : [TacticsBW.exploit_element_in_result] *)
(* Test case : *)

(*Require Import (* fixme : retirer l'Import *) IdTransformation.*)

 Import ClassMetamodel RelationalMetamodel Class2Relational.

Goal forall (cm : ClassModel)
  (i : nat)
  (n : string)
  (H : In 
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
  idtac "Test case : .".

  intros.
  Succeed 
    tryif 
      TacticsBW.exploit_element_in_result H ; [] ;
      solve [eauto]
    then test_success
    else test_failure.

Abort.

End Test1.
