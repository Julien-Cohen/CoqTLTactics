Require Import Bool.

Definition beq_bool := eqb.

Ltac destruct_conjunctions := 
  repeat (
      match goal with   
        [ H : ?e && _ = true |- _ ] => apply Bool.andb_true_iff in H ; destruct H  
      end).
