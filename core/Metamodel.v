(** * Metamodel **)
Require Import core.Model.
Require Import core.EqDec.

Class Metamodel :=
{
    ModelElement: Type;
    ModelLink: Type;
    
    elements_eqdec: ModelElement -> ModelElement -> bool; (* FIXME : no semantics with respect to equality *)

    (* Decidable Equality*)
    elements_eqb := elements_eqdec; (* FIXME : remove-me *)

    InstanceModel := Model ModelElement ModelLink;
}.
