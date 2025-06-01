From Stdlib Require Import String.
From Stdlib Require Import EqNat.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.

Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import transformations.Moore2Mealy.Moore.
Require Import transformations.Moore2Mealy.Moore2Mealy.
Require Import core.properties.injectivity.Injectivity_elem.
Require Import core.properties.injectivity.Injectivity_link.
Require Import core.properties.injectivity.Utils.

(*************************************************************)
(** * Injectivity of  CoqTL                                   *)
(** * Using operational semantics                            *)
(*************************************************************)



(** Injectivity *)

Definition Injective {tc: TransformationConfiguration} (tr: Transformation) :=
 forall sm1 sm2,
  Model_equiv (execute tr sm1) (execute tr sm2) ->
    Model_equiv sm1 sm2.  

Definition Injective_alt {tc: TransformationConfiguration} (tr: Transformation) :=
 forall sm1 sm2,
  (execute tr sm1) = (execute tr sm2) ->
     sm1  = sm2.  

Lemma union_elem_link {tc: TransformationConfiguration} : 
  forall tr, 
    Injectivity_elem tr ->
    Injectivity_link tr ->
    Injective tr.
Proof.  
  unfold Injectivity_elem, Injectivity_link, Injective.
  intros.
   apply set_eq_Model_equiv.
    + apply H.  apply Model_equiv_set_eq_elem. assumption.
    + apply H0. apply Model_equiv_set_eq_link. assumption.  
Qed.


