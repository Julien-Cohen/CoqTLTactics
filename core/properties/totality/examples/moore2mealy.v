Require Import String.
Require Import EqNat.
Require Import List.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.

Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.Certification.
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import transformations.Moore2Mealy.Moore.
Require Import transformations.Moore2Mealy.Mealy.
Require Import transformations.Moore2Mealy.Moore2Mealy.

Require Import core.properties.totality.totality.


(*************************************************************)
(** * Totality of CoqTL                                      *)
(*************************************************************)

(** directly instantiate Totality on Moore2Mealy             *)

Theorem Moore2Mealy_Totality_elem_test :
forall (sm : MooreModel) (te : MealyMetamodel_Object),
  (exists (sp : list MooreMetamodel_Object),
      In sp (allTuples Moore2Mealy sm) /\
      In te (instantiatePattern Moore2Mealy sm sp)) ->
      In te (allModelElements (execute Moore2Mealy sm)).
Proof.
    apply Totality_elem.
Qed.


(** apply Totality on more realistic user theorem            *)

Theorem Moore2Mealy_Totality_elem_test3 :
forall (sm : MooreModel) (te : Mealy.State),
    let mealystate := (MealyMetamodel_toObject Mealy.StateClass te) in
      (exists (se: Moore.State),
        let moorestate := (MooreMetamodel_toObject Moore.StateClass se) in
          In [moorestate] (allTuples Moore2Mealy sm) /\
          In mealystate (instantiatePattern Moore2Mealy sm [moorestate])) -> 
          In mealystate (allModelElements (execute Moore2Mealy sm)).
Proof.
intros.
assert (exists (sp : list MooreMetamodel_Object),
          In sp (allTuples Moore2Mealy sm) /\
            In mealystate (instantiatePattern Moore2Mealy sm sp)).
{
  destruct H.
  remember (MooreMetamodel_toObject Moore.StateClass x) as e.
  exists ([e]).
  crush.
}
apply Totality_elem in H0.
exact H0.
Qed.


