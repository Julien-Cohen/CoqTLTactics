(** * Metamodel **)
Require Import core.Model.
Require Import core.EqDec.

Class Sum (SumType: Type) (SubTypeName: Type):=
  {
    denoteSubType: SubTypeName -> Set;
    toSubType: forall (t: SubTypeName), SumType -> option (denoteSubType t);
    toSumType: forall (t: SubTypeName), (denoteSubType t) -> SumType;

  }.

Class Metamodel (ModelElement: Type) (ModelLink: Type) (ModelClass: Type) (ModelReference: Type) :=
{
    elements: Sum ModelElement ModelClass;
    links: Sum ModelLink ModelReference;

    elements_eqdec: EqDec ModelElement;
    
    (* Denotation *)
    denoteModelClass: ModelClass -> Set := denoteSubType;
    denoteModelReference: ModelReference -> Set := denoteSubType;
  
    (* Downcasting *)
    toModelClass: forall (t:ModelClass), ModelElement -> option (denoteModelClass t) := toSubType;
    toModelReference: forall (t:ModelReference), ModelLink -> option (denoteModelReference t) := toSubType;
  
    (* Upcasting *)
    toModelElement: forall (t: ModelClass), (denoteModelClass t) -> ModelElement := toSumType;
    toModelLink: forall (t: ModelReference), (denoteModelReference t) -> ModelLink := toSumType;

}.

Definition hasType {ModelElement ModelLink ModelClass ModelReference: Type} {mm: Metamodel ModelElement ModelLink ModelClass ModelReference}  (t: ModelClass) (e: ModelElement) : bool :=
  match (toModelClass t e) with
  | Some e' => true
  | _ => false
  end.
