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
 Require Import EvalExpressions.
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
In a0 (instantiateOnPiece (buildTransformation n (a :: l)) sm1 sp) <->
In a0 (instantiateOnPiece (buildTransformation n [a]) sm1 sp) \/
In a0 (instantiateOnPiece (buildTransformation n l) sm1 sp).
Proof.
intros.
split.
+ intro.
  unfold instantiateOnPiece in H.
  unfold instantiateRuleOnPiece  in H.
  unfold instantiateIterationOnPiece in H.
  unfold matchingRules in H.
  simpl in H.
  unfold instantiateOnPiece.
  unfold instantiateRuleOnPiece.
  unfold instantiateIterationOnPiece.
  unfold matchingRules.
  simpl. 
  remember ((fun r : Rule =>
  flat_map
    (fun iter : nat =>
     flat_map
       (fun o : OutputPatternUnit =>
        optionToList (instantiateElementOnPiece o sm1 sp iter))
       r.(r_outputPattern))
    (seq 0 (evalIteratorExpr r sm1 sp)))) as f.
  remember (filter (fun r : Rule => evalGuardExpr r sm1 sp) l) as l1.
  destruct (evalGuardExpr a sm1 sp) eqn: ca.
  - apply in_flat_map in H.
    destruct H. destruct H.
    destruct H.
    -- rewrite <- H in H0. left. apply in_flat_map. exists x. crush.
    -- right. apply in_flat_map. exists x. crush.
  - right. auto.
+ intro.
unfold instantiateOnPiece.
unfold instantiateRuleOnPiece.
unfold instantiateIterationOnPiece.
unfold matchingRules.
simpl. 
remember ((fun r : Rule =>
flat_map
  (fun iter : nat =>
   flat_map
     (fun o : OutputPatternUnit =>
      optionToList (instantiateElementOnPiece o sm1 sp iter))
     r.(r_outputPattern))
  (seq 0 (evalIteratorExpr r sm1 sp)))) as f.
remember (filter (fun r : Rule => evalGuardExpr r sm1 sp) l) as l1.
destruct (evalGuardExpr a sm1 sp) eqn: ca.
++ destruct H.
- unfold instantiateOnPiece in H.
unfold instantiateRuleOnPiece in H.
unfold instantiateIterationOnPiece in H.
unfold matchingRules in H.
simpl in H.
rewrite ca in H.
rewrite <- Heqf in H.
apply in_flat_map in H. destruct H.
apply in_flat_map. exists x. split. crush. crush. 
- unfold instantiateOnPiece in H.
unfold instantiateRuleOnPiece in H.
unfold instantiateIterationOnPiece in H.
unfold matchingRules in H.
simpl in H.
rewrite <- Heqf in H.
apply in_flat_map in H.
destruct H.
apply in_flat_map.
exists x. split; crush.
++ destruct H. 
unfold instantiateOnPiece in H.
unfold instantiateRuleOnPiece in H.
unfold instantiateIterationOnPiece in H.
unfold matchingRules in H.
simpl in H.
rewrite ca in H.
rewrite <- Heqf in H.
simpl in H. inversion H.
unfold instantiateOnPiece in H.
unfold instantiateRuleOnPiece in H.
unfold instantiateIterationOnPiece in H.
unfold matchingRules in H.
simpl in H.
rewrite <- Heqf in H.
apply in_flat_map in H.
destruct H.
apply in_flat_map.
exists x. split; crush.
Qed.

(** ** maxArity **)

(*Lemma tr_maxArity_in :
  forall (eng: TransformationEngine),
    forall (tr: Transformation) (r: Rule),
      In r (getRules tr) ->
      maxArity tr >= length (getInTypes r).
Proof.
  intros. apply max_list_upperBound. do 2 apply in_map. exact H.
Qed.

Theorem incl_equiv_to_surj:
  forall (eng: TransformationEngine),
    (forall (tr: Transformation) (sm : SourceModel)
       (sp : list SourceModelElement) (tp: list TargetModelElement) (tp1: list TargetModelElement)
       (r : Rule),
        instantiateRuleOnPiece r tr sm sp = Some tp1 ->
        In r (matchingRules tr sm sp) ->
        instantiateOnPiece tr sm sp = Some tp ->
        incl tp1 tp) <->
    (forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tp: list TargetModelElement) (te : TargetModelElement),
        instantiateOnPiece tr sm sp = Some tp ->
        (exists (r : Rule) (tp1 : list TargetModelElement),
            In r (matchingRules tr sm sp) /\
            instantiateRuleOnPiece r tr sm sp = Some tp1 /\
            In te tp1) ->
        In te tp).
Proof.
  split.
  - intros.
    destruct H1. destruct H1. destruct H1. destruct H2.
    + pose (H tr sm sp tp x0 x H2 H1 H0).
      apply i in H3.
      assumption.
  - intros.
    unfold incl.
    intros.
    pose (H tr sm sp tp a H2).
    apply i.
    exists r, tp1.
    split. assumption.
    split. assumption.
    assumption.
Qed.

Theorem tr_match_functionality :
  forall (eng: TransformationEngine)
    (tr: Transformation) (sm : SourceModel) (sp : list SourceModelElement) (r1: list Rule) (r2: list Rule),
          matchingRules tr sm sp  = r1 -> matchingRules tr sm sp = r2 -> r1 = r2.
Proof.
    intros.
    rewrite H in H0.
    inversion H0.
    reflexivity.
Qed.

Theorem tr_matchingRules_None_tr : forall t: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      getRules tr = nil ->
      matchingRules tr sm sp = nil.
Proof.
  intros.
  destruct (matchingRules tr sm sp) eqn:mtch. reflexivity.
  exfalso.
  pose (tr_matchingRules_in tr sm sp r).
  rewrite H in i.
  pose (in_eq r l).
  rewrite <- mtch in i0.
  apply i in i0.
  simpl in i0.
  destruct i0.
  contradiction.
Qed.

  Theorem tr_matchingRules_non_Nil :
    forall eng: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel),
    forall (sp : list SourceModelElement),
      (matchingRules tr sm sp) <> nil <->
      (exists (r: Rule),
        In r (getRules tr) /\
        matchRuleOnPiece r tr sm sp = return true).
  Proof.
    intros.
    split.
    + intro.
      assert (exists (r: Rule), In r (matchingRules tr sm sp)).
      {
        destruct (matchingRules tr sm sp).
        ++ crush.
        ++ exists r.
           crush.
      }
      destruct H0.
      rename x into r.
      exists r.
      apply tr_matchingRules_in. auto.
    + intro.
      destruct H.
      apply tr_matchingRules_in in H.
      destruct (matchingRules tr sm sp).
      ++ inversion H.
      ++ crush.
  Qed.

Theorem tr_instantiateOnPiece_None_tr : forall t: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      getRules tr = nil ->
      (instantiateOnPiece tr sm sp = None).
Proof.
  intros.
  destruct (instantiateOnPiece tr sm sp) eqn:dst.
  - apply tr_matchingRules_None_tr with (sm:=sm) (sp:=sp) in H.
    assert (instantiateOnPiece tr sm sp <> None). { rewrite dst. discriminate. }
    apply tr_instantiateOnPiece_non_None in H0.
    destruct H0. destruct H0.
    rewrite H in H0.
    destruct H0.
  - reflexivity.
Qed.

Theorem tr_applyPattern_None_tr :
  forall t: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        getRules tr = nil ->
        (applyPattern tr sm sp = None).
Proof.
  intros.
  destruct (applyPattern tr sm sp) eqn:dst.
  - apply tr_matchingRules_None_tr with (sm:=sm) (sp:=sp) in H.
    assert (applyPattern tr sm sp <> None). { rewrite dst. discriminate. }
    apply tr_applyPattern_non_None in H0.
    destruct H0. destruct H0.
    rewrite H in H0.
    destruct H0.
  - reflexivity.
Qed.

Theorem tr_execute_None_tr_elements : forall t: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel),
      getRules tr = nil ->
      allModelElements (execute tr sm) = nil.
Proof.
  intros.
  destruct (allModelElements (execute tr sm)) eqn:ame.
  - reflexivity.
  - exfalso.
    pose (tr_execute_in_elements tr sm t0).
    pose (in_eq t0 l).
    rewrite <- ame in i0.
    apply i in i0.
    destruct i0. destruct H0. destruct H0. destruct H1.
    pose (tr_instantiateOnPiece_in tr sm x t0).
    apply tr_matchingRules_None_tr with (sm:=sm) (sp:=x) in H.
    destruct i0. destruct H3.
    -- exists x0.
       split. assumption. assumption.
    -- destruct H3.
       destruct H3.
       rewrite H in H3.
       contradiction.
Qed.

  Theorem tr_execute_non_Nil_elements :
   forall eng: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel),
      (allModelElements (execute tr sm)) <> nil <->
      (exists (te : TargetModelElement) (sp : list SourceModelElement) (tp : list TargetModelElement),
          incl sp (allModelElements sm) /\
          instantiateOnPiece tr sm sp = Some tp /\
          In te tp).
  Proof.
    intros.
    split.
    + intro.
      assert (exists (te: TargetModelElement), In te (allModelElements (execute tr sm))).
      {
        destruct (allModelElements (execute tr sm)).
        ++ crush.
        ++ exists t.
           crush.
      }
      destruct H0.
      rename x into te.
      exists te.
      apply tr_execute_in_elements. auto.
    + intro.
      destruct H.
      apply tr_execute_in_elements in H.
      destruct (allModelElements (execute tr sm)).
      ++ inversion H.
      ++ crush.
  Qed.


  Theorem tr_execute_non_Nil_links :
   forall eng: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel) ,
      (allModelLinks (execute tr sm)) <> nil <->
      (exists (tl : TargetModelLink) (sp : list SourceModelElement) (tpl : list TargetModelLink),
          incl sp (allModelElements sm) /\
          applyPattern tr sm sp = Some tpl /\
          In tl tpl).
  Proof.
    intros.
    split.
    + intro.
      assert (exists (tl: TargetModelLink), In tl (allModelLinks (execute tr sm))).
      {
        destruct (allModelLinks (execute tr sm)).
        ++ crush.
        ++ exists t.
           crush.
      }
      destruct H0.
      rename x into tl.
      exists tl.
      apply tr_execute_in_links. auto.
    + intro.
      destruct H.
      apply tr_execute_in_links in H.
      destruct (allModelLinks (execute tr sm)).
      ++ inversion H.
      ++ crush.
  Qed.

Theorem tr_execute_None_tr_links : forall t: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel),
      getRules tr = nil ->
      allModelLinks (execute tr sm) = nil.
Proof.
  intros.
  destruct (allModelLinks (execute tr sm)) eqn:aml.
  - reflexivity.
  - exfalso.
    pose (tr_execute_in_links tr sm t0).
    pose (in_eq t0 l).
    rewrite <- aml in i0.
    apply i in i0.
    destruct i0. destruct H0. destruct H0. destruct H1.
    pose (tr_applyPattern_in tr sm x t0).
    apply tr_matchingRules_None_tr with (sm:=sm) (sp:=x) in H.
    destruct i0. destruct H3.
    -- exists x0.
       split. assumption. assumption.
    -- destruct H3.
       destruct H3.
       rewrite H in H3.
       contradiction.
Qed.

Theorem tr_applyElementOnPiece_None :
   forall eng: TransformationEngine,
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat) (ope: OutputPatternUnit (getInTypes r) (getIteratorType r)),
        length sp <> length (getInTypes r) ->
        applyElementOnPiece r ope tr sm sp i = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  assert (exists (tl: list TargetModelLink), applyElementOnPiece r ope tr sm sp i = Some tl).
  { specialize (option_res_dec (applyElementOnPiece r ope tr sm sp)). intros.
    specialize (H1 i H0). destruct H1. exists x. crush. }
  destruct H1.
  assert (exists oper,  In oper (getOutputLinks  (getInTypes r) (getIteratorType r) ope) /\  applyLinkOnPiece r ope oper tr sm sp i <> None).
  { specialize (tr_applyElementOnPiece_non_None tr r sm sp i ope). intros. crush. }
  destruct H2.
  assert ( applyLinkOnPiece r ope x0 tr sm sp i = None).
  { specialize (tr_applyLinkOnPiece_None tr sm r sp i ope x0). intros. crush. }
  crush.
Qed.

Theorem tr_applyIterationOnPiece_None :
   forall eng: TransformationEngine,
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
        length sp <> length (getInTypes r) ->
        applyIterationOnPiece r tr sm sp i = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  assert (exists (tl: list TargetModelLink), applyIterationOnPiece r tr sm sp i = Some tl).
  { specialize (option_res_dec (applyIterationOnPiece r tr sm sp)). intros.
    specialize (H1 i H0). destruct H1. exists x. crush. }
  destruct H1.
  assert (exists  ope : OutputPatternUnit (getInTypes r) (getIteratorType r),
      In ope (getOutputPattern r) /\ applyElementOnPiece r ope tr sm sp i <> None).
  { specialize (tr_applyIterationOnPiece_non_None tr r sm sp i). crush. }
  destruct H2.
  destruct H2.
  assert ( applyElementOnPiece r x0 tr sm sp i = None).
  { specialize (tr_applyElementOnPiece_None eng tr sm r sp i x0). intros. crush. }
  crush.
Qed.

Theorem tr_applyRuleOnPiece_None :
   forall eng: TransformationEngine,
      forall (tr: Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
        length sp <> length (getInTypes r) ->
        applyRuleOnPiece r tr sm sp = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  assert (exists (tl: list TargetModelLink), applyRuleOnPiece r tr sm sp = Some tl).
  { specialize (option_res_dec (applyRuleOnPiece r tr sm)). intros.
    specialize (H1 sp H0). destruct H1. exists x. crush. }
  destruct H1.
  assert (exists (i: nat), i < length (evalIterator r sm sp) /\ applyIterationOnPiece r tr sm sp i <> None).
  { specialize (tr_applyRuleOnPiece_non_None tr r sm sp). crush. }
  destruct H2.
  destruct H2.
  assert (applyIterationOnPiece r tr sm sp x0 = None).
  { specialize (tr_applyIterationOnPiece_None eng tr sm r sp x0). crush. }
  crush.
Qed.

Theorem tr_instantiateIterationOnPiece_None :
   forall eng: TransformationEngine,
     forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
        length sp <> length (getInTypes r) ->
        instantiateIterationOnPiece r sm sp i = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  assert (exists (tp: list TargetModelElement), instantiateIterationOnPiece r sm sp i = Some tp).
  { specialize (option_res_dec (instantiateIterationOnPiece r sm sp)). intros.
    specialize (H1 i H0). destruct H1. exists x. crush. }
  destruct H1.
  assert (exists  ope : OutputPatternUnit (getInTypes r) (getIteratorType r),
      In ope (getOutputPattern r) /\ instantiateElementOnPiece r ope sm sp i <> None).
  { specialize (tr_instantiateIterationOnPiece_non_None r sm sp i). crush. }
  destruct H2.
  destruct H2.
  assert ( instantiateElementOnPiece r x0 sm sp i = None).
  { specialize (tr_instantiateElementOnPiece_None sm r sp i x0). intros. crush. }
  crush.
Qed.

Theorem tr_instantiateRuleOnPiece_None :
  forall eng: TransformationEngine,
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
      length sp <> length (getInTypes r) ->
      instantiateRuleOnPiece r tr sm sp = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  assert (exists (tp: list TargetModelElement), instantiateRuleOnPiece r tr sm sp = Some tp).
  { specialize (option_res_dec (instantiateRuleOnPiece r tr sm)). intros.
    specialize (H1 sp H0). destruct H1. exists x. crush. }
  destruct H1.
  assert (exists (i: nat), i < length (evalIterator r sm sp) /\ instantiateIterationOnPiece r sm sp i <> None).
  { specialize (tr_instantiateRuleOnPiece_non_None tr r sm sp). crush. }
  destruct H2.
  destruct H2.
  assert (instantiateIterationOnPiece r sm sp x0 = None).
  { specialize (tr_instantiateIterationOnPiece_None eng sm r sp x0). crush. }
  crush.
Qed.

Theorem tr_instantiateIterationOnPiece_None_iterator :
 forall eng: TransformationEngine,
  forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
      i >= length (evalIterator r sm sp) ->
      instantiateIterationOnPiece r sm sp i = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  specialize (tr_instantiateIterationOnPiece_non_None r sm sp i).
  intros.
  destruct H1.
  specialize (H1 H0).
  destruct H1. destruct H1.
  specialize (tr_instantiateElementOnPiece_None_iterator sm r sp x H).
  crush.
Qed.

Theorem tr_applyElementOnPiece_None_iterator :
  forall eng: TransformationEngine,
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat) (ope: OutputPatternUnit (getInTypes r) (getIteratorType r)),
      i >= length (evalIterator r sm sp) ->
      applyElementOnPiece r ope tr sm sp i = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  specialize (tr_applyElementOnPiece_non_None tr r sm sp i ope).
  intros.
  destruct H1.
  specialize (H1 H0).
  destruct H1. destruct H1.
  specialize (tr_applyLinkOnPiece_None_iterator tr sm r sp).
  intros.
  specialize (H4 i ope x H).
  crush.
Qed.

Theorem tr_applyIterationOnPiece_None_iterator :
   forall eng: TransformationEngine,
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
      i >= length (evalIterator r sm sp) ->
      applyIterationOnPiece r tr sm sp i = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  specialize (tr_applyIterationOnPiece_non_None tr r sm sp i).
  intros.
  destruct H1.
  specialize (H1 H0).
  destruct H1. destruct H1.
  specialize (tr_applyElementOnPiece_None_iterator eng tr sm r sp i x H).
  crush.
Qed.
*)
