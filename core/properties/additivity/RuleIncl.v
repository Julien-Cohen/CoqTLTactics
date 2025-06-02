Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
From Stdlib Require Import String.
From Stdlib Require Import EqNat.
From Stdlib Require Import List.
Require Import core.utils.Utils.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.
Require Import AxiomaticSemantics.


Require Import core.properties.additivity.Moore2Mealy_Additivity_link_witness.
Require Import core.properties.additivity.sampleMoore_additivity_link.


(*************************************************************)
(** * Additivity in Rule context (Link)                      *)
(** * Using operational semantics                            *)
(*************************************************************)

From Stdlib Require Import Logic.Classical_Pred_Type.


Definition Transformation_incl_rules {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (t1.(arity) = t2.(arity)) /\ 
  forall r: Rule, In r t1.(rules) -> In r t2.(rules).
