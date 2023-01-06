Require Import String.

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
