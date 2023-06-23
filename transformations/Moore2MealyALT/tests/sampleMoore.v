Require Import List.
Require Import core.Model.
Require Import String.
Require Import transformations.Moore2MealyALT.Moore.
Open Scope string_scope.

Import Id.

(* S0("a") --"A"-> S1("b") --"B"-| 
                      /\         |
                       |         |
                       -----------
*)


Definition id0 := Id "S0".
Definition id1 := Id "S1".

Definition InputModel : Model Moore.MM :=
  let t0 := Build_Transition_t id0 "A" id1 in 
  let t1 := Build_Transition_t id1 "B" id1 in
  let s0 := Build_State_t id0 "a" in
  let s1 := Build_State_t id1 "b" in
  Build_Model Moore.MM
    (
      (TransitionElement t0) :: 
	(StateElement s0) :: 
	(StateElement s1) :: 
	(TransitionElement t1) :: 
	nil
    )
    (	nil
    )
.
