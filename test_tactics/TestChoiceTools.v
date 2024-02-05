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

    List.In r T.(Syntax.rules) /\ r.(Syntax.r_name) = "state". 
Proof.
  idtac "Testing ChoiceTools.rule_named".
  idtac "Test case : a rule with the corresponding name is/is not in the transformation.".

  intros. eexists.

  
(* Success of the tactic expected *)
  Succeed (first [
      solve [split ; [ChoiceTools.rule_named "state" | reflexivity]] ; 
      test_success
    | test_failure]).

(* Failure of the tactic expected with incorrect parameters *)
 Succeed first [ 
     split ; [ChoiceTools.rule_named "transition" | reflexivity] ; 
      test_failure 
    | test_success].

(* Failure of the tactic expected with incorrect parameters *)
 Succeed first [ 
     split ; [ChoiceTools.rule_named "other" | reflexivity] ; 
      test_failure 
    | test_success].

Abort.

