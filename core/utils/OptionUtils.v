Require Import String.
Require Import NotationUtils.

Definition is_option_eq 
  {A: Type} (oe : option A) 
  (e1 : A) (beq : A -> A -> bool) : bool :=
  match oe with 
  | Some e => beq e1 e
  | None => false
  end.
  
Definition valueOption {A: Type} (a: option A) (default: A) : A := 
  match a with
    | None => default
    | Some s => s
  end.

Class ValueOption (A: Type) := {
   value : option A -> A
}.

Instance ValueString : ValueOption string := {
   value (a: option string) := valueOption a ""%string
}.


Local Ltac inj H := injection H ; clear H ; intros ; subst.



Ltac monadInv H :=
  let N := fresh "E" in
  
  match type of H with 

  |  _ <- ?E ; Some _ = Some _ => 
      destruct E eqn:N ;
      [ inj H | discriminate H ] ; 
      let N2 := fresh H in
      rename N into N2
             
  | _ <- ?E ; _ = Some _ => 
      destruct E eqn:N ;
      [  | discriminate H ]

  | option_map _ _ = Some _ =>
      unfold option_map in H ; monadInv H

  end.

Ltac monadInvN n H :=
  unfold n in H ; monadInv H.
