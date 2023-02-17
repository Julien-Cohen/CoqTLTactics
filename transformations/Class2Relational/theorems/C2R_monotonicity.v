Require Import String.

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

Theorem All_classes_instantiate_impl :
  Monotonicity Class2Relational.
Proof.
  (* In this proof I use the same script an in other proofs, but I need to use some lemmas, that I don't need in the two first proofs. Why ? *)
  

  unfold Monotonicity.
  unfold TargetModel_elem_incl. unfold SourceModel_elem_incl.
  unfold incl.
  intros sm1 sm2 INC a IN.

  (* (1) *)
  destruct (Tactics.destruct_in_modelElements_execute_lem IN) 
    as (r & sp & n & ope & IN_E & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & IN'). 

  (* (2)  *)
  Tactics.progress_in_In_rules IN_RULE ; [ | ] ;


  (* (3) make the ouput-pattern-element appear *)
  Tactics.progress_in_ope IN_OP ; 

  (* (4) *) 
  Tactics.exploit_evalGuard MATCH_GUARD ;

  
  (* (5) *)
  Tactics.exploit_evaloutpat IN' ;
  
  (* (6) *)
  clear IN_IT ;

  (* 7 *)
   Semantics.exploit_in_allTuples IN_E.

  {
    apply INC in IN_E.
    destruct t0.
    eapply Elements.transform_class_fw (* why ? *) ; eauto.
  }
  {
    C2RTactics.negb_inv MATCH_GUARD.
    destruct t0 ; simpl in MATCH_GUARD. 
    subst derived.
    apply INC in IN_E.
    eapply Elements.transform_attribute_fw (* why ? *) ; eauto.
  }    
Qed.



 
(** Generalisation ? If the guard depends only on the input element and not on the other elements of the input model, then the transformation s monotonic ? *)


