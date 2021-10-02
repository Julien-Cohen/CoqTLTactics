Set Implicit Arguments.
Scheme Equality for list.


(** * Model
  Each model is constructed by a list of {@code ModelElement} and {@ModelLink}. **)

Class Model (ModelElement: Type) (ModelLink: Type) :=
  {
    modelElements : list ModelElement;
    modelLinks : list ModelLink;
  }.

Definition allModelElements {ModelElement: Type} {ModelLink: Type} (m: Model ModelElement ModelLink) : list ModelElement :=
  (@modelElements _ _ m).

Definition allModelLinks {ModelElement: Type} {ModelLink: Type} (m: Model ModelElement ModelLink) : list ModelLink :=
  (@modelLinks _ _ m).

(*
 allModelElements and allModelLinks are fields of record Model.
 To use them on a Model m:
 @allModelElements _ _ a.
 *)

Definition Model_beq {ME ML: Type} (ME_beq: ME -> ME -> bool) (ML_beq: ML -> ML -> bool) (m1 m2: Model ME ML) :=
  andb (list_beq ME_beq (@modelElements _ _ m1) (@modelElements _ _ m2))
  (list_beq ML_beq (@modelLinks _ _ m1) (@modelLinks _ _ m2)).

Definition Model_wellFormed {ME ML: Type} (ME_beq: ME -> ME -> bool) (ML_beq: ML -> ML -> bool) (m: Model ME ML): Prop :=
  (modelLinks <> nil) -> (modelElements <> nil).