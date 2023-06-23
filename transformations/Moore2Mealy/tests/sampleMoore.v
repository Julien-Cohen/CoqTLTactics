Require Import List.
Require Import core.Model.
Require Import String.
Require Import transformations.Moore2Mealy.Moore.
Open Scope string_scope.

(* S0("a") --"A"-> S1("b") --"B"-| 
                      /\         |
                       |         |
                       -----------
*)

Definition InputModel : Model Moore.MM :=
  let t0 := Build_Transition_t 0 "A" in 
  let t1 := Build_Transition_t 1 "B" in
  let s0 := Build_State_t "S0" "a" in
  let s1 := Build_State_t "S1" "b" in
  Build_Model Moore.MM
    (
      (TransitionElement t0) :: 
	(StateElement s0) :: 
	(StateElement s1) :: 
	(TransitionElement t1) :: 
	nil
    )
    (
      (Transition_sourceLink (Build_Transition_source_t t0 s0)) ::
	(Transition_targetLink (Build_Transition_target_t t0 s1)) ::
	(Transition_sourceLink (Build_Transition_source_t t1 s1)) ::
	(Transition_targetLink (Build_Transition_target_t t1 s1)) ::
	nil
    )
.
