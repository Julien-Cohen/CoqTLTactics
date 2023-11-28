(************************************************************************)
(*         *   The NaoMod Development Team                              *)
(*  v      *   INRIA, CNRS and contributors - Copyright 2017-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**
 This file is an auxilary file for type class for relational transformation
    engine.

 We give here lemmas that can be directly derived from type class [core.Engine]

 **)


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

(*********************************************************)
(** * Metatheorems for relational Transformation Engines *)
(*********************************************************)



(* decompose instantiateOnPiece results *)
Lemma instantiateOnPiece_distributive:
  forall (tc: TransformationConfiguration),
  forall a0 sp sm1 n a l,
    In a0 (produced_elements (traceTrOnPiece (buildTransformation n (a :: l)) sm1 sp)) <->
      In a0 (produced_elements (traceTrOnPiece (buildTransformation n [a]) sm1 sp)) \/
        In a0 (produced_elements (traceTrOnPiece (buildTransformation n l) sm1 sp)).
Proof.
  intros.
  unfold traceTrOnPiece, traceRuleOnPiece, matchingRules, produced_elements.  
  repeat rewrite map_flat_map.
  simpl.
  split ; intro H.
  + remember (filter (fun r : Rule => evalGuard r sm1 sp) l) as l1.
    destruct (evalGuard a sm1 sp) eqn: ca.
    - apply in_flat_map in H.
      destruct H. destruct H.
      destruct H.
      -- rewrite <- H in H0. left. apply in_flat_map. exists x. crush.
      -- right. apply in_flat_map. exists x. crush.
    - right. auto.
  + destruct (evalGuard a sm1 sp) eqn: ca.
      ++    simpl in H.
            destruct H.
         -- rewrite <- app_nil_end in H. 
            unfold traceRuleOnPiece in H.
            rewrite map_flat_map in H.
            apply in_flat_map in H. destruct H as (x, (H,H0)).
            simpl flat_map ; apply in_or_app ; left.
            unfold traceRuleOnPiece.
            rewrite map_flat_map.
            apply in_flat_map.
            exists x ; auto.
         -- apply in_flat_map in H. destruct H as (x, (H, H0)).
            simpl flat_map ; apply in_or_app ; right.
            apply in_flat_map.
            exists x. split. crush. crush.
      ++ destruct H. 
         -- simpl in H.
            contradiction.
         -- assumption. 
Qed.

