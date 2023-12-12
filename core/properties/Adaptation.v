Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import UserExpressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import Coq.Program.Basics.

(* Trivial theorem if we are free to choose anything *)

Theorem adaptation :
forall (tc: TransformationConfiguration) 
  (T_t: Type) (sem_t: TargetModel -> T_t)
  (adapter: Transformation),
  exists (T_s: Type) (sem_s: SourceModel -> T_s) (f: T_s -> T_t), 
     compose sem_t (execute adapter) = compose f (sem_s).
Proof.
  intros.
  exists T_t, (compose sem_t (execute adapter)), id.
  crush.
Qed.

(* Trivial theorem, version for views *)

Theorem adaptation'' :
forall (tc: TransformationConfiguration) 
  (T_t: Type) (adapter: Transformation),
  exists (view_t: TargetModel -> TargetModel) (view_s: SourceModel -> SourceModel),
     compose view_t (execute adapter) = compose (execute adapter) view_s.
Proof.
  intros.
  exists id, id.
  crush.
Qed.

