(** Utilities for tactics that need backtracking *)


From core 
  Require Import Model.



Ltac multi_eassumption :=
    multimatch goal with
      | [ H : List.In _ (modelElements _) |- _ ] => exact H 
    end.

Ltac incl_singleton :=
  apply ListUtils.incl_singleton ; 
  multimatch goal with
    [ H : List.In _ _ |- _ ] => exact H 
                            
    (* multimatch is important here because it allows backtracking, as opposed to eassumption. Here, if there are two hypothesis in the context that allow to solve the goal, because of evar in the goal, if the the selected hypothesis instanciates the evar so that the following tactics fail, it will backtrack and select another one.  This situation can be explored in the proof of Moore2MEaly/theorems/Links/source_link_fw (use move to switch the order of hypothesis) *)

  end.


(* When a guard is applied to an input piece that does not match the expected type, evaluation of the guard will lead to false = true.
   This tacic detects this situation and fails when it occurs. Such a failure should be used to trigger a backtrack. *)
Ltac fail_on_type_mismatch :=
  tryif 
    compute ;
    match goal with 
      [ |- false = true]  => idtac 
    end 
  then fail 
  else idtac.

Ltac fail_on_False :=
  tryif 
    simpl ; 
    match goal with 
      [ |- False] => idtac 
    end 
  then fail 
  else idtac.
