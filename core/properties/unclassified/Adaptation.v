Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
From Stdlib Require Import String.
From Stdlib Require Import EqNat.
From Stdlib Require Import List.
Require Import UserExpressions.
Require Import core.utils.Utils.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Program.Basics.

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
  reflexivity.
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
  reflexivity.
Qed.

