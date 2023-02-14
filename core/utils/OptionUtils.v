Require Import String.
Require Import NotationUtils.
Require PropUtils.

Definition is_option_eq 
  {A: Type} (oe : option A) 
  (e1 : A) (beq : A -> A -> bool) : bool :=
  match oe with 
  | Some e => beq e1 e
  | None => false
  end.
  
Lemma is_option_eq_true :
  forall T (a:option T) b c, 
  is_option_eq a b c = true ->
  exists r, a = Some r /\ c b r = true .
Proof.
  unfold is_option_eq.
  intros T a b c H.
  destruct a ; [ | discriminate ].
  eauto.
Qed.

Ltac is_option_eq_inv H :=
  match type of H with
    | is_option_eq ?A _ _ = true =>
        apply is_option_eq_true in H ;
        let NEW := fresh H in
        destruct H as (? & (H & NEW))
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


Ltac monadInv H :=
  match type of H with 

  |  _ <- ?E ; Some _ = Some _ => 
       let N := fresh "EQ" in
       
       destruct E eqn:N ; 
       [ PropUtils.inj H | discriminate H];
       rename N into H
         
  | _ <- ?E ; _ = Some _ => 
      let N := fresh "E" in

      destruct E eqn:N ;
      [  | discriminate H ]
        
  | option_map _ _ = Some _ =>
      unfold option_map in H ; monadInv H

  end.

Ltac monadInvN n H :=
  unfold n in H ; monadInv H.
