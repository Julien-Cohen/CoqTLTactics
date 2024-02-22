Require Import IdTransformation TestUtils.

Require ChoiceTools.


Import 
  List Model String NotationUtils Semantics PoorTraceLink  NotationUtils Semantics.

Import BasicMetamodel.
Import NotationUtils.

Open Scope string_scope. 

(* Test 1. *)
(* Tactic under test : rule_named *)
(* Test case : a rule with the corresponding name is in the transformation. *)
Goal 
  forall (m : BasicMetamodel.M)
         (s : BasicMetamodel.Node_t)
         (IN1 : In (Node s) (modelElements m)),
  exists r,

    List.In r Id_T.(Syntax.rules) /\ r.(Syntax.r_name) = "state". 
Proof.
  intros. eexists.

  tested_tactic "ChoiceTools.rule_named".
  test_case "A rule with the corresponding name is/is not in the transformation.".

  
(* Success of the tactic expected *)
  Succeed 
    tryif
      solve [split ; [ChoiceTools.rule_named "state" | reflexivity]]  
    then test_success
    else test_failure.

  test_case "A rule with the corresponding name is/is not in the transformation (with incorrect parameters).".

(* Failure of the tactic expected with incorrect parameters *)
 Succeed 
   tryif 
     split ; [ChoiceTools.rule_named "transition" | reflexivity ]  
   then test_failure 
   else test_success.
 
(* Failure of the tactic expected with incorrect parameters *)
 Succeed 
   tryif
     split ; [ChoiceTools.rule_named "other" | reflexivity]
   then test_failure 
   else test_success.

Abort.

