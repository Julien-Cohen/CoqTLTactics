
Require Eqdep.

(** *** Logic *)

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


(** *** Basic mecanisms on goals and hypothesis *)

(** Variant of the injection tactic. *)
Ltac inj H := injection H ; clear H ; intros ; subst.

Ltac destruct_match_H H :=
  match type of H with 
     | context[match ?P with | _ => _ end] => destruct P eqn:?
  end. 

Ltac destruct_match_G :=
  match goal with 
     [ |- context[match ?P with | _ => _ end]] => destruct P 
  end. 

Ltac destruct_if_hyp :=
  let E := fresh "E" in
 match goal with
        [ H : context[if ?B then _ else _] |- _ ] => destruct B eqn:E 
 end.

Ltac destruct_if_goal :=
  let E := fresh "E" in
 match goal with
        [ |- context[if ?B then _ else _] ] => destruct B eqn:E 
 end.

(* To replace the [inversion] tactics on equalities on a dependant type constructor. *)
Ltac dep_inversion H := 
  let H':= fresh H in
  inversion H as [H'] ; apply Eqdep.EqdepTheory.inj_pair2 in H'.

  
Ltac duplicate H1 H2 := remember H1 as H2 eqn:TMP ; clear TMP.

Ltac unif H1 H2 :=
  rewrite H1 in H2 ; inj H2.
