(** * Metamodel **)
Require Import core.Model.
Require Import core.Metamodel.

Class Sum (T: Type) (K: Type):=
  {
    denoteSubType: K -> Set;
    toSubType: forall (k: K), T -> option (denoteSubType k);
    toSumType: forall (k: K), (denoteSubType k) -> T;

  }.

Class ModelingMetamodel (mm : Metamodel) :=
{
    EKind: Type;
    LKind: Type;
    elements: Sum mm.(ModelElement) EKind;
    links: Sum mm.(ModelLink) LKind;
    
    (* Denotation *)
    denoteEKind: EKind -> Set := denoteSubType;
    denoteLKind: LKind -> Set := denoteSubType;
  
    (* Downcasting *)
    toEKind: forall (t:EKind), mm.(ModelElement) -> option (denoteEKind t) := toSubType;
    toLKind: forall (t:LKind), mm.(ModelLink) -> option (denoteLKind t) := toSubType;
  
    (* Upcasting *)
    toModelElement: forall (t: EKind), (denoteEKind t) -> mm.(ModelElement) := toSumType;
    toModelLink: forall (t: LKind), (denoteLKind t) -> mm.(ModelLink) := toSumType;

}.

Definition hasType {mm: Metamodel} {mmm: ModelingMetamodel mm} (t: EKind) (e: mm.(ModelElement)) : bool :=
  match (toEKind t e) with
  | Some _ => true
  | _ => false
  end.
