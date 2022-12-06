(** * Metamodel **)


Record Metamodel :=
{
    ModelElement: Type;
    ModelLink: Type;
    
    elements_eqdec: ModelElement -> ModelElement -> bool; (* FIXME : no semantics with respect to equality *)

}.
