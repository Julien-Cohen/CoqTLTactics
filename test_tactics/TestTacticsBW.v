Require Import  TestUtils.


Require TacticsBW.


Import 
  List Model String NotationUtils Semantics PoorTraceLink  NotationUtils Semantics.

(*Require Import BasicMetamodel.*)

Open Scope string_scope.




(* Test 1. *)
(* Tactic under test : [TacticsBW.exploit_element_in_result] *)
(* Test case : *)

(*Require Import (* fixme : retirer l'Import *) IdTransformation.*)

Require Import Class2Relational.Class2Relational.

Goal forall (cm : ClassMetamodel.ClassModel)
  (i : nat)
  (n : string)
  (H : In 
         (RelationalMetamodel.TableElement 
            {|
              RelationalMetamodel.Table_id := i;
              RelationalMetamodel.Table_name := n 
            |})
         (modelElements (execute Class2Relational cm))),

  exists c, 
    In (ClassMetamodel.ClassElement c) (modelElements cm) 
     /\ c.(ClassMetamodel.Class_id) = i 
     /\ c.(ClassMetamodel.Class_name) = n.
  
Proof.
  idtac "Testing TacticsBW.exploit_element_in_result".
  idtac "Test case : .".

  intros.
  Succeed (
      tryif solve [TacticsBW.exploit_element_in_result H ; [] ; eauto]
      then test_success
      else test_failure
    ).

Abort.

