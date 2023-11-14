(** Generic type for Links *)

Record Glue A B := { left_glue : A ; right_glue : B}.
Scheme Equality for Glue. (* Never used ? *)

Arguments left_glue {A} {B}.
Arguments right_glue {A} {B}.


Notation "'glue' a 'with' b" :=  ({| left_glue := a ; right_glue := b |}) (right associativity, at level 60). 

Notation "'do_glue' a 'with' b" :=   (Some {| left_glue := a ; right_glue := b |}) (right associativity, at level 60). 
