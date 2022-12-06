(********************************************************************
	@name Coq declarations for model
	@date 2022/01/29 15:46:30
	@description Automatically generated by XMI2Coq transformation.
 ********************************************************************)
		 
 Require Import List.
 Require Import core.Model.
 Require Import String.
 Require Import transformations.Moore2Mealy.Moore.
 Open Scope string_scope.
 
(* Moore models as counterexample to prove distributivity of CoqTL *)

 

Definition Moore_m1 : Model MooreMetamodel_Metamodel_Instance :=
    (Build_Model MooreMetamodel_Metamodel_Instance
       (
        (Build_MooreMetamodel_Object TransitionClass (BuildTransition  "0")) :: 
        (Build_MooreMetamodel_Object TransitionClass (BuildTransition  "1")) :: nil
       )
       (
           nil
       )
    ).

Definition Moore_m2 : Model MooreMetamodel_Metamodel_Instance :=
       (Build_Model MooreMetamodel_Metamodel_Instance
           (
               (Build_MooreMetamodel_Object StateClass (BuildState  "S0" "1")) :: 
               (Build_MooreMetamodel_Object StateClass (BuildState  "S1" "0")) ::  
               nil
           )
           (
               (Build_MooreMetamodel_Link TransitionSourceReference (BuildTransitionSource (BuildTransition  "0") (BuildState  "S1" "0"))) ::
               (Build_MooreMetamodel_Link TransitionTargetReference (BuildTransitionTarget (BuildTransition  "0") (BuildState  "S0" "1"))) ::
               (Build_MooreMetamodel_Link TransitionSourceReference (BuildTransitionSource (BuildTransition  "1") (BuildState  "S0" "1"))) ::
               (Build_MooreMetamodel_Link TransitionTargetReference (BuildTransitionTarget (BuildTransition  "1") (BuildState  "S1" "0"))) ::
               nil
           )
       ).
