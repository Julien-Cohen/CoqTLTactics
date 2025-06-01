From Stdlib Require Import 
  String 
  EqNat 
  List 
  PeanoNat 
  Lia 
  FunctionalExtensionality.

Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require        core.Certification.
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.



(*************************************************************)
(** * Functionality (or determinism) of  CoqTL                *)
(** * Using operational semantics                            *)
(*************************************************************)


Theorem functionality {tc: TransformationConfiguration} :
    forall (tr: Transformation) (sm1 sm2: SourceModel),
       sm1 = sm2 -> (execute tr sm1) = (execute tr sm2).
Proof.
    congruence.
Qed.

Definition strong_functionality {tc: TransformationConfiguration} :=
  forall (tr: Transformation) (sm1 sm2: SourceModel),
    Model_equiv sm1 sm2 -> Model_equiv (execute tr sm1) (execute tr sm2).














