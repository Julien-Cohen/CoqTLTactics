Require Import core.utils.CpdtTactics.


Theorem contraposition : forall p q:Prop, (p->q)->(~q->~p).
Proof.
  intros p q Hi Hnq Hp. exact (Hnq (Hi Hp)).
Qed.

Ltac destruct_or H :=
  match type of H with _ \/ _ =>
     destruct H as [ H | H ]
  end.

Ltac remove_or_false H := 
  match type of H with 
    _ \/ False => destruct H as [ H | H ] ; [ | contradiction] 
  end. 

Ltac remove_or_false_auto :=
  match goal with 
    [ H : _ \/ False |- _ ] => remove_or_false H
  end.


Ltac inj H := injection H ; clear H ; intros ; subst.
