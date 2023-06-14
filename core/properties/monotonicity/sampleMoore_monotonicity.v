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
 

(* Moore models as counterexample to prove monotonicity of CoqTL *)


 Definition Moore_m1 : Model Metamodel_Instance :=
     (Build_Model Metamodel_Instance
        (
            (StateElement (BuildState  "S0" "1")) :: nil
        )
        (
            nil
        )
     ).
 
Definition Moore_m2 : Model Metamodel_Instance :=
        (Build_Model Metamodel_Instance
            (
                (TransitionElement (BuildTransition  "0")) :: 
                (TransitionElement (BuildTransition  "1")) ::
                (StateElement (BuildState  "S0" "1")) :: 
                (StateElement (BuildState  "S1" "0")) ::  
                nil
            )
            (
                (TransitionSourceLink (BuildTransitionSource (BuildTransition  "0") (BuildState  "S1" "0"))) ::
		        (TransitionTargetLink (BuildTransitionTarget (BuildTransition  "0") (BuildState  "S0" "1"))) ::
                (TransitionSourceLink (BuildTransitionSource (BuildTransition  "1") (BuildState  "S0" "1"))) ::
		        (TransitionTargetLink (BuildTransitionTarget (BuildTransition  "1") (BuildState  "S1" "0"))) ::
                nil
            )
        ).
