Require Import String.
Open Scope string_scope.

Require Import core.utils.Utils.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.properties.monotonicity.Monotonicity.

From transformations.Class2Relational
  Require Import 
  Class2Relational
  ClassMetamodel
  RelationalMetamodel
  C2RTactics.



From transformations.Class2Relational.theorems
  Require Elements.

Theorem c2r_monotonicity :
  Monotonicity Class2Relational.
Proof.
  (* In this proof I use the same script an in other proofs, but I need to use some lemmas, that I don't need in the two first proofs. Why ? *)
  

  unfold Monotonicity.
  unfold TargetModel_elem_incl. unfold SourceModel_elem_incl.
  unfold incl.
  intros sm1 sm2 INC a IN.

  (*  We have to deduce something in the transformed model from something in the transformed model.
      To do this we deduce something in the source model from the fact on the transformed model, and then we deduce the expected result on the transformed model from the fact deduced on the source model. 
      This is why we can see FW and BW reasonning below. *) 

  TacticsBW.exploit_element_in_result IN ; [ | ].

  {
    apply INC in IN_ELTS0.
    destruct e.
    TacticsFW.in_modelElements_singleton_fw_tac "Class2Table" "tab" 0 IN_ELTS0 ; reflexivity.
  }
  {
    C2RTactics.negb_inv MATCH_GUARD.
    destruct e ; simpl in MATCH_GUARD. 
    subst Attribute_derived.
    apply INC in IN_ELTS0.
    TacticsFW.in_modelElements_singleton_fw_tac "Attribute2Column" "col" 0 IN_ELTS0 ; reflexivity.
  }    
Qed.



 
(** Generalisation ? If the guard depends only on the input element and not on the other elements of the input model, then the transformation s monotonic ? *)


