(** * Metamodel **)
Require Import core.Model.

Class Metamodel :=
{
    ModelElement: Type;
    ModelLink: Type;
    
    (* Decidable Equality*)
    elements_eqdec: forall (x y : ModelElement), {x = y} + {x <> y};
    elements_eqb (x y: ModelElement) := if elements_eqdec x y then true else false;

    InstanceModel := Model ModelElement ModelLink;
}.
