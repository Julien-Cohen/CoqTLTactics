Set Implicit Arguments.
Require Import List.
Scheme Equality for list.


(** * Model
  Each model is constructed by a list of {@code ModelElement} and {@ModelLink}. **)

Record Model (ModelElement: Type) (ModelLink: Type) :=
  {
    modelElements : list ModelElement;
    modelLinks : list ModelLink;
  }.

Definition Model_beq {ME ML: Type} (ME_beq: ME -> ME -> bool) (ML_beq: ML -> ML -> bool) (m1 m2: Model ME ML) :=
  andb (list_beq ME_beq m1.(modelElements) m2.(modelElements))
  (list_beq ML_beq m1.(modelLinks) m2.(modelLinks)).

Definition Model_wellFormed {ME ML: Type} (m: Model ME ML): Prop :=
  m.(modelElements) = nil -> m.(modelLinks) = nil.

(*Definition Model_incl {ME ML: Type} (m1 m2: Model ME ML) := 
  forall (e:ME) (l:ML),
   count_occ' _ m1.(modelElements) e <= count_occ' _ m2.(modelElements) e /\
   count_occ' _ m1.(modelLinks) l <= count_occ' _ m2.(modelLinks) l.

Definition Model_equiv {ME ML: Type} (m1 m2: Model ME ML)  := 
  forall (e:ME) (l:ML),
  count_occ' _ m1.(modelElements) e = count_occ' _ m2.(modelElements) e /\
  count_occ' _ m1.(modelLinks) l = count_occ' _ m2.(modelLinks) l. *)

Definition Model_app {ME ML: Type} (m1 m2: Model ME ML) := 
  Build_Model 
    (app m1.(modelElements) m2.(modelElements))
    (app m1.(modelLinks) m2.(modelLinks)).

Definition Model_concat {ME ML: Type} (ms: list (Model ME ML)) := 
  Build_Model 
    (flat_map (@modelElements _ _ ) ms)
    (flat_map (@modelLinks _ _) ms).
