Set Implicit Arguments.
Require Import List.
Scheme Equality for list.

Require ListUtils.

Require Import Metamodel.

(** * Model
  Each model is constructed by a list of {@code ModelElement} and {@ModelLink}. **)

Record Model (MM:Metamodel) :=
  {
    modelElements : list MM.(ModelElement);
    modelLinks : list MM.(ModelLink);
  }.

Definition Model_beq {MM: Metamodel} (ML_beq: MM.(ModelLink) -> MM.(ModelLink) -> bool) (m1 m2: Model MM) :=
  andb (list_beq MM.(elements_eqdec) m1.(modelElements) m2.(modelElements))
  (list_beq ML_beq m1.(modelLinks) m2.(modelLinks)).

Definition Model_wellFormed {MM: Metamodel} (m: Model MM): Prop :=
  m.(modelElements) = nil -> m.(modelLinks) = nil.

Local Notation count := ListUtils.count_occ_b.

Definition Model_incl {MM : Metamodel} (m1 m2: Model MM) := 
  forall e,
   count MM.(elements_eqdec) m1.(modelElements) e <= count MM.(elements_eqdec) m2.(modelElements) e /\
   forall l,
   count MM.(links_eqdec) m1.(modelLinks) l <= count MM.(links_eqdec) m2.(modelLinks) l.
   
Definition Model_equiv {MM : Metamodel} (m1 m2: Model MM)  := 
  forall e,
  count MM.(elements_eqdec) m1.(modelElements) e = count MM.(elements_eqdec) m2.(modelElements) e /\
  forall l,
  count MM.(links_eqdec) m1.(modelLinks) l = count MM.(links_eqdec) m2.(modelLinks) l. 

Definition Model_app {MM: Metamodel} (m1 m2: Model MM) := 
  {| 
    modelElements := app m1.(modelElements) m2.(modelElements) ;
    modelLinks := app m1.(modelLinks) m2.(modelLinks)
  |}.

Definition Model_concat {MM: Metamodel} (ms: list (Model MM)) := 
  {|
    modelElements := flat_map (@modelElements _) ms ;
    modelLinks := flat_map (@modelLinks _) ms
  |}.

