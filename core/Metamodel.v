(** * Metamodel **)


Record Metamodel :=
{
    ElementType: Type;
    LinkType: Type;
    
    elements_eqdec: ElementType -> ElementType -> bool; (* FIXME : no semantics with respect to equality *)
    links_eqdec: LinkType -> LinkType -> bool; 

}.
