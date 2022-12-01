(** * Metamodel **)
Require Import core.Model.

Class Metamodel :=
{
    ModelElement: Type;
    ModelLink: Type;
    
    elements_eqdec: ModelElement -> ModelElement -> bool; (* FIXME : no semantics with respect to equality *)

    InstanceModel := Model ModelElement ModelLink;
}.
