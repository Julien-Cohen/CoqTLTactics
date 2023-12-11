(** Generic type for Links *)

Record Glue A B := { src : A ; trg : B}.
Scheme Equality for Glue. (* Never used ? *)

Arguments src {A} {B}.
Arguments trg {A} {B}.


Notation "'glue' a 'with' b" :=  ({| src := a ; trg := b |}) (right associativity, at level 60). 

Notation "'do_glue' a 'with' b" :=   (Some {| src := a ; trg := b |}) (right associativity, at level 60). 
