(** Generic type for Links *)

Record Glue {A} {B} := { lglue : A ; rglue : B}.
Scheme Equality for Glue. (* Never used ? *)
