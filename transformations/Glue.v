(** Generic type for Links *)

Record Glue A B := { left_glue : A ; right_glue : B}.
Scheme Equality for Glue. (* Never used ? *)

Arguments left_glue {A} {B}.
Arguments right_glue {A} {B}.
