(** * Metamodel **)
Require Import core.Model.
Require Import core.Metamodel.

Class Sum (SumType: Type) (SubTypeName: Type):=
  {
    denoteSubType: SubTypeName -> Set;
    toSubType: forall (t: SubTypeName), SumType -> option (denoteSubType t);
    toSumType: forall (t: SubTypeName), (denoteSubType t) -> SumType;

  }.

Class ModelingMetamodel `(mm : Metamodel) :=
{
    ModelClass: Type;
    ModelReference: Type;
    elements: Sum mm.(ModelElement) ModelClass;
    links: Sum mm.(ModelLink) ModelReference;
    
    (* Denotation *)
    denoteModelClass: ModelClass -> Set := denoteSubType;
    denoteModelReference: ModelReference -> Set := denoteSubType;
  
    (* Downcasting *)
    toModelClass: forall (t:ModelClass), mm.(ModelElement) -> option (denoteModelClass t) := toSubType;
    toModelReference: forall (t:ModelReference), mm.(ModelLink) -> option (denoteModelReference t) := toSubType;
  
    (* Upcasting *)
    toModelElement: forall (t: ModelClass), (denoteModelClass t) -> mm.(ModelElement) := toSumType;
    toModelLink: forall (t: ModelReference), (denoteModelReference t) -> mm.(ModelLink) := toSumType;

}.

Definition hasType {mm: Metamodel} {mmm: ModelingMetamodel mm} (t: ModelClass) (e: mm.(ModelElement)) : bool :=
  match (toModelClass t e) with
  | Some _ => true
  | _ => false
  end.
