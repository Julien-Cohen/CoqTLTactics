(** * Metamodel **)
Require Import core.Model.
Require Import core.Metamodel.


(** Consider a metamodel where the type T below is used.
   
   Parameter a : Type.  
   Parameter b : Type.

   Inductive T := Cons_A of a | Cons_B of b. 

   We call terms of type T "elements" or "links".
   We call a and b "datatypes". We call terms of type a or b "raw data".

  In transformation rules, we have to express patterns on elements (or links). To do this we use a type which abstracts the cases in T, here the type K below.

   Inductive K := A | B. 

   We call the constructors/terms A and B "kinds".
   
   The class Sum T K expresses the correspondance between T and K. 
*)  


Class Sum (T: Type) (K: Type):=
  {
    denoteDatatype: K -> Set;
    toRawData: forall (k: K), T -> option (denoteDatatype k);
    constuctor: forall (k: K), (denoteDatatype k) -> T;
    instanceof : K -> T -> bool :=
      fun k d => match toRawData k d with Some _ => true | None => false end                             
  }.


(** Metamodels contain elements and links, so a "correspondance" for a metamodel is built from two "kinds" and their two correspondances. *) 

Class ModelingMetamodel (mm : Metamodel) :=
{
    EKind: Type;
    LKind: Type;
    elements: Sum mm.(ElementType) EKind;
    links: Sum mm.(LinkType) LKind;
    
    (* Denotation *)
    denoteEDatatype: EKind -> Set := elements.(denoteDatatype);
    denoteLDatatype: LKind -> Set := links.(denoteDatatype);
  
    (* Downcasting *)
    toEData: forall (k:EKind), mm.(ElementType) -> option (denoteEDatatype k) := elements.(toRawData) ;
    toLData: forall (k:LKind), mm.(LinkType) -> option (denoteLDatatype k) := links.(toRawData); (* not used *)
  
    (* Upcasting *)
    toModelElement: forall (k: EKind), (denoteEDatatype k) -> mm.(ElementType) := elements.(constuctor) ;
    toModelLink: forall (k: LKind), (denoteLDatatype k) -> mm.(LinkType) := links.(constuctor);

}.


