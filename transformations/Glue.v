(** Generic type for Links *)

Record Glue {A} {B} := { l_glue : A ; r_glue : B}.
Scheme Equality for Glue. (* Never used ? *)
