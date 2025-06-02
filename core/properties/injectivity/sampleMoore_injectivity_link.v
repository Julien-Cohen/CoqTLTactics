
		 
From Stdlib  Require Import List.
 Require Import core.Model.
From Stdlib  Require Import String.
 Require Import transformations.Moore2Mealy.Moore.
 Open Scope string_scope.
 
Import Glue.

(* Moore models as counterexample to disprove injectivity of CoqTL *)


 Definition Moore_m1 : Model Moore.MM :=
    (Build_Model Moore.MM
        (
            (Transition (Build_Transition_t 0 "0000")) :: 
            (State (Build_State_t  (Id.Id "S0000") "1111")) :: 
            (State (Build_State_t  (Id.Id "S1111") "0000")) ::  
            nil
        )
        (
            (TransitionSource (Build_Glue _ _ (Build_Transition_t 0 "0000") (Build_State_t  (Id.Id "S1111") "0000"))) ::
            (TransitionTarget (Build_Glue _ _ (Build_Transition_t 0 "0000") (Build_State_t  (Id.Id "S0000") "1111"))) ::
            nil
        )
).
 
Definition Moore_m2 : Model Moore.MM :=
    (Build_Model Moore.MM
        (
            (Transition (Build_Transition_t 0 "0")) :: 
            (State (Build_State_t  (Id.Id "S0") "1")) :: 
            (State (Build_State_t  (Id.Id "S1") "0")) ::  
            nil
        )
        (
            (TransitionSource (Build_Glue _ _ (Build_Transition_t 0 "0") (Build_State_t  (Id.Id "S1") "0"))) ::
            (TransitionTarget (Build_Glue _ _ (Build_Transition_t 0 "0") (Build_State_t  (Id.Id "S0") "1"))) ::
            nil
        )
    ).

