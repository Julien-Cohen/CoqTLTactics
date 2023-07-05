Set Implicit Arguments.
Require Import List.

Require Import ListUtils.

Require Import Metamodel.

(** * Model
  Each model is constructed by a list of {@code ElementType} and {@LinkType}. **)

Record Model (MM:Metamodel) :=
  {
    modelElements : list MM.(ElementType);
    modelLinks : list MM.(LinkType);
  }.

Definition Model_wellFormed {MM: Metamodel} (m: Model MM): Prop :=
  m.(modelElements) = nil -> m.(modelLinks) = nil.


Definition Model_incl {MM : Metamodel} (m1 m2: Model MM) : Prop :=
  (forall e,
    List.In e m1.(modelElements) ->  List.In e m2.(modelElements))
  /\
   (forall l,
       List.In l m1.(modelLinks) -> List.In l m2.(modelLinks) ).
   
Definition Model_equiv {MM : Metamodel} (m1 m2: Model MM) : Prop := 
  Model_incl m1 m2 /\ Model_incl m2 m1.

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

