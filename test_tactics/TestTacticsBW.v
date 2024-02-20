Require Import  TestUtils.

Require TacticsBW.

Import 
  List Model String NotationUtils Semantics PoorTraceLink  NotationUtils.

Open Scope string_scope.

Require BasicMetamodel IdTransformation Class2Relational.Class2Relational.


(** Tests for tactics on elements. *)

Section TestElement1.

(* Tactic under test : [TacticsBW.exploit_element_in_result] *)
(* Test case : *)

  Import BasicMetamodel IdTransformation.

Context 
    (cm : M) 
    (i : nat)
    (H : In 
                  (Node {| Node_id := i |})
                  (modelElements (execute T cm))).

  Goal   False.  
       
  
  Proof.
    idtac "Testing TacticsBW.exploit_element_in_result".
    idtac "Test case : ".

  tryif
    TacticsBW.exploit_element_in_result H 
  then
   match goal with 
    | [ _ : In (Node {| Node_id := i |}) (modelElements cm) |- _ ] => test_success  
    | _ => test_failure
    end 
  
  else test_failure.
    
  Abort.
  
End TestElement1.


Section TestElement2.

(* Tactic under test : [TacticsBW.exploit_element_in_result] *)
(* Test case : *)

  Import ClassMetamodel RelationalMetamodel Class2Relational.

  Context 
    (cm : ClassModel) 
    (i : nat) 
    (n : string)
  
    (H : In 
                  (TableElement 
                     {|
                       Table_id := i;
                       Table_name := n 
                     |})
                  (modelElements (execute Class2Relational cm))).

  Goal
    exists c, 
      In (ClassElement c) (modelElements cm) 
      /\ c.(Class_id) = i 
      /\ c.(Class_name) = n.
  
  Proof.
    idtac "Testing TacticsBW.exploit_element_in_result".
    idtac "Test case : ".

    tryif 
      TacticsBW.exploit_element_in_result H ; [] ;
      eexists ; split ; [ | split ; [ | ]] ; 
      [ eassumption | reflexivity | reflexivity ]  
    then test_success
    else test_failure.
    
  Abort.
  
End TestElement2.


Section TestElement2ALT.

(* Tactic under test : [TacticsBW.exploit_element_in_result] *)
(* Test case : *)

  Import ClassMetamodel RelationalMetamodel Class2Relational.

  Context 
    (cm : ClassModel) 
    (i : nat) 
    (n : string)
 
    (H : In 
           (TableElement {| Table_id := i; Table_name := n |})
           (modelElements (execute Class2Relational cm))).

  Goal False.
  
  Proof.
    idtac "Testing TacticsBW.exploit_element_in_result".
    idtac "Test case : The generated hypothesis contains all the information on the source element.".

  tryif
    TacticsBW.exploit_element_in_result H 
  then
   match goal with 
    | [ _ : In (ClassElement {| Class_id := i ; Class_name := n|}) (modelElements cm) |- _ ] => 
          test_success  
    | _ => test_failure
    end 
  
  else test_failure.
      
  Abort.
  
End TestElement2ALT.


(** Tests for tactics on links. *)

Section TestLink1.

(* Tactic under test : [TacticsBW.exploit_link_in_result] *)
(* Test case : *)

  Import ClassMetamodel RelationalMetamodel Class2Relational.
  Import Glue.
  
  Context
    (cm : ClassModel) 
    (c : Column_t) 
    (tb : Table_t)
    (R_IN1 : In (Column_referenceLink (glue c with tb))
                 (modelLinks (execute Class2Relational cm))).

  Goal 
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
  

    tryif 
      TacticsBW.exploit_link_in_result R_IN1 ; [] ;
      eexists ; eexists ; split ; [ | split ; [ | split ; [ | split]]] ;
      [ eassumption | eassumption | eassumption | eassumption | unfold RelationalMetamodel.get_E_data in EQ ; congruence ]
    then test_success
    else test_failure.
    
  Abort.
  

End TestLink1.
