Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import Expressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.


(*************************************************************)
(** * Monotonicity                                           *)
(*************************************************************)

Lemma incl_flat_map:
forall {A B : Type} (f : A -> list B) (l1 l2 : list A),
  incl l1 l2 ->
    incl (flat_map f l1) (flat_map f l2).
Proof.
  unfold incl.
  intros A B f l1 l2 incl_src e in_ps1.
  apply in_flat_map.
  apply in_flat_map in in_ps1.
  destruct in_ps1 as [p1 in_ps1]. 
  destruct in_ps1 as [in_p1_ps1 in_e_inst].
  exists p1.
  specialize (incl_src p1 in_p1_ps1) as incl_src.
  split. 
  exact incl_src.
  exact in_e_inst.
Qed.

Theorem mono_instantiate:
forall (tc: TransformationConfiguration) (tr: Transformation) (sm: SourceModel) ps1 ps2,
  incl ps1 ps2->
    incl (flat_map (instantiatePattern tr sm) ps1) 
         (flat_map (instantiatePattern tr sm) ps2).
Proof.
  intros.
  apply incl_flat_map.
  exact H.
Qed.

Theorem mono_apply:
forall (tc: TransformationConfiguration) (tr: Transformation) (sm: SourceModel) ps1 ps2,
  incl ps1 ps2->
    incl (flat_map (applyPattern tr sm) ps1) 
         (flat_map (applyPattern tr sm) ps2).
Proof.
  intros.
  apply incl_flat_map.
  exact H.
Qed.

Theorem mono_alltuple:
forall (tc: TransformationConfiguration) (tr: Transformation) (sm1 sm2 : SourceModel),
  incl (allModelElements sm1) (allModelElements sm2)->
    incl (allTuples tr sm1) (allTuples tr sm2).
Proof.
  unfold incl, allTuples.
  intros.
  apply tuples_up_to_n_incl_length.
  apply tuples_up_to_n_incl in H0.
  unfold incl in *.
  crush.
  apply tuple_length in H0.
  auto.
Qed.

Definition Model_incl {ME ML: Type} (sm1 sm2: Model ME ML) := 
  incl (allModelElements sm1) (allModelElements sm2) /\
  incl (allModelLinks sm1) (allModelLinks sm2).

Definition mono_eval_guard (tc: TransformationConfiguration) (tr: Transformation) (sm1 sm2 : SourceModel) :=
  incl (allModelElements sm1) (allModelElements sm2) ->
  forall r sp,
    In r (Transformation_getRules tr) ->
      (Rule_getGuardExpr r) sm1 sp = Some true ->
      (Rule_getGuardExpr r) sm2 sp = Some true.  

Example mono_eval_guard_ex:
  forall (tc: TransformationConfiguration) (tr: Transformation) (sm1 sm2 : SourceModel),
    incl (allModelElements sm1) (allModelElements sm2)->
    forall sp,
    (fun (m: SourceModel) (sp: list SourceModelElement) => Some true) sm1 sp = Some true ->
    (fun (m: SourceModel) (sp: list SourceModelElement) => Some true) sm2 sp = Some true.
Proof.
  crush.
Qed.

Theorem mono_match:
forall (tc: TransformationConfiguration) (tr: Transformation) (sm1 sm2 : SourceModel),
  incl (allModelElements sm1) (allModelElements sm2) ->
  mono_eval_guard tc tr sm1 sm2 ->
  forall sp, In sp (allTuples tr sm1) ->
    incl (matchPattern tr sm1 sp) (matchPattern tr sm2 sp).
Proof.
  intros.
  unfold mono_eval_guard in H0.
  specialize (H0 H).
  unfold incl.
  intros.
  unfold matchPattern in *.
  apply filter_In.
  apply filter_In in H2.
  destruct H2.
  split. auto.
  unfold matchRuleOnPattern in *.
  destruct (evalGuardExpr a sm1 sp) eqn: guard.
  unfold evalGuardExpr in guard.
  unfold evalExpr in guard.
  destruct b.
  specialize (H0 a sp H2 guard).
  destruct (evalGuardExpr a sm2 sp) eqn: guard'.
  unfold evalGuardExpr in guard'.
  unfold evalExpr in guard'.
  destruct b.
  auto.
  rewrite H0 in guard'.
  inversion guard'.
  unfold evalGuardExpr in guard'.
  unfold evalExpr in guard'.
  rewrite H0 in guard'.
  inversion guard'.
  inversion H3.
  inversion H3.
Qed.


Theorem mono_instantiate':
forall (tc: TransformationConfiguration) (tr: Transformation) (sm1 sm2 : SourceModel),
  incl (allModelElements sm1) (allModelElements sm2) ->
    incl 
      (flat_map (instantiatePattern tr sm1) (allTuples tr sm1)) 
      (flat_map (instantiatePattern tr sm2) (allTuples tr sm2)).
Proof.
  intros.
  unfold incl.
  intros.
  apply in_flat_map.
  apply in_flat_map in H0. destruct H0. destruct H0.
  exists x.
  split. admit.
  apply in_flat_map.
  apply in_flat_map in H1. destruct H1. destruct H1.
  exists x0.
  split.

  Print evalExpr .
  simpl in guard.
Admitted.
          


Theorem mono_execute:
forall (tc: TransformationConfiguration) (tr: Transformation) (sm1 sm2 : SourceModel),
  incl (allModelElements sm1) (allModelElements sm2)->
  Model_incl (execute tr sm1) (execute tr sm2).
Admit.

  
 
  










