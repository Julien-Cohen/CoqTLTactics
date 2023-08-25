Require Import List.
Require Import core.Model.
Require Import String.
Require Import transformations.Moore2Mealy.Moore.
Open Scope string_scope.

Import Id Glue.

(* S0("a") --"A"-> S1("b") --"B"-| 
                      /\         |
                       |         |
                       -----------
*)


Definition id0 := Id "S0".
Definition id1 := Id "S1".

Definition InputModel : Model Moore.MM :=
  let t0 := Build_Transition_t 0 "A" in 
  let t1 := Build_Transition_t 1 "B" in
  let s0 := Build_State_t id0 "a" in
  let s1 := Build_State_t id1 "b" in
  Build_Model Moore.MM
    (
      (Transition t0) :: 
	(State s0) :: 
	(State s1) :: 
	(Transition t1) :: 
	nil
    )
    (
      (TransitionSource (Build_Glue _ _ t0 s0)) ::
	(TransitionTarget (Build_Glue _ _ t0 s1)) ::
	(TransitionSource (Build_Glue _ _ t1 s1)) ::
	(TransitionTarget (Build_Glue _ _ t1 s1)) ::
	nil
    )
.
