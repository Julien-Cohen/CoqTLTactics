

Require Import String.
Require Import EqNat.
Require Import List.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.

Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.properties.confluence.basicExpressions.
Require Import core.properties.confluence.basicSemantics.
Require Import core.properties.confluence.basicSyntax.
Require Import core.utils.Utils.


(*************************************************************)
(** * Confluence of CoqTL  (Model)                           *)
(** * Using operational semantics                            *)
(*************************************************************)


Section Confluence.
Context (tc: TransformationConfiguration).

Definition disjoint_rules tr : Prop :=
  forall r1 r2, 
   In r1 tr ->
   In r2 tr ->
    forall sm sp, 
    matchRuleOnPattern r1 sm sp = true ->
    matchRuleOnPattern r2 sm sp = true ->
      r1 = r2.

(* Set semantics: we think that the list of rules represents a set (we don't allow two rules to have the same name)*)

Definition Transformation_permutation  (t1 t2: basicSyntax.Transformation) := 
  (basicSyntax.Transformation_getArity t1 = basicSyntax.Transformation_getArity t2) /\ 
  set_eq (basicSyntax.Transformation_getRules t1) (basicSyntax.Transformation_getRules t2).

(** Deprecated (use Model_equiv, see equiv_equiv below)*)
Definition TargetModel_equiv (m1 m2: TargetModel) :=
  (forall (e: TargetElementType) ,
   (In e m1.(modelElements) <-> In e m2.(modelElements))) /\
 (forall (l: TargetLinkType),
    (In l m1.(modelLinks) <-> In l m2.(modelLinks))).


Lemma equiv_equiv : forall m1 m2, TargetModel_equiv m1 m2 <-> Model_equiv m1 m2.
Proof.
  unfold TargetModel_equiv, Model_equiv.
  unfold Model_incl.
  intros.
  split ; intro H.
  + destruct H. split.
    - split ; intros.
      * specialize (H e).
        apply H ; auto.
      * specialize (H0 l). apply H0 ; auto.
    - split ; intros.
      * specialize (H e).
        apply H ; auto.
      * specialize (H0 l). apply H0 ; auto.
  + destruct H. 
    destruct H.
    destruct H0.
      split ; intro ; split ; intro ; auto.
Qed.

Definition Confluent (t1: basicSyntax.Transformation) :=
    forall (sm: SourceModel) (t2:basicSyntax.Transformation),
    Transformation_permutation t1 t2 -> 
    Model_equiv (execute t1 sm) (execute t2 sm).


(* General definition but not holding for CoqTL *)
Definition Confluence := 
  forall (t: basicSyntax.Transformation),
    Confluent t. 

Definition WeakConfluence :=
   forall (t: basicSyntax.Transformation),
    disjoint_rules (basicSyntax.Transformation_getRules t)  ->
      Confluent t.

Lemma disjoint_rules_of_transformation_permutation :
  forall (t1 t2: basicSyntax.Transformation),
    disjoint_rules (basicSyntax.Transformation_getRules t1)  ->
    Transformation_permutation t1 t2 ->
    disjoint_rules (basicSyntax.Transformation_getRules t2).
Proof.
  intros.
  unfold disjoint_rules in *.
  intros.
  unfold Transformation_permutation in H0.
  destruct H0.
  unfold set_eq in H5.
  destruct H5.
  unfold incl in H6.
  assert (include_r1 := H6 r1 H1).
  assert (include_r2 := H6 r2 H2).
  specialize (H r1 r2 include_r1 include_r2 sm sp H3 H4).
  assumption.
Qed.

Lemma resolveIter_eq :
forall (t1 t2: basicSyntax.Transformation),
disjoint_rules (basicSyntax.Transformation_getRules t1)  ->
disjoint_rules (basicSyntax.Transformation_getRules t2)  ->
Transformation_permutation t1 t2 ->
   resolveIter t1 = resolveIter t2.
Proof.
intros t1 t2 disjoint_rules_t1 disjoint_rules_t2 tr_eq.
unfold resolveIter.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
rename x into sm.
rename x1 into sp.
rename x2 into iter.
rename x0 into opname.

remember (fun r : basicSyntax.Rule =>
matchRuleOnPattern r sm sp) as find_cond.
remember (basicSyntax.Transformation_getRules t1) as rs1.
remember (basicSyntax.Transformation_getRules t2) as rs2.

assert (find find_cond rs1 = find find_cond rs2).
{
  destruct (find find_cond rs1) eqn: find_ca1.
  destruct (find find_cond rs2) eqn: find_ca2.
  + apply List.find_some in find_ca1.
    apply List.find_some in find_ca2.
  f_equal.
  unfold Transformation_permutation in tr_eq.
  destruct tr_eq.
  destruct H0.
  assert (In r rs2). {  unfold incl in H0. crush. }
  destruct find_ca2.
  destruct find_ca1.
  rewrite Heqfind_cond in H6.
  rewrite Heqfind_cond in H4.
  unfold disjoint_rules in disjoint_rules_t2.
  specialize (disjoint_rules_t2 r r0 H2 H3 sm sp H6 H4) as witness.
  exact witness.
  + apply List.find_some in find_ca1.
    specialize (List.find_none find_cond rs2 find_ca2).
    intro.
    unfold Transformation_permutation in tr_eq.
    destruct tr_eq.
    destruct H0.
    assert (In r rs2). { unfold set_eq in H1. destruct H1. unfold incl in H0. crush. }
    specialize (H r H0). crush.
  + destruct (find find_cond rs2) eqn: find_ca2.
  ++ apply List.find_some in find_ca2.
     specialize (List.find_none find_cond rs1 find_ca1).
     intro.
     unfold Transformation_permutation in tr_eq.
     destruct tr_eq.
     destruct H0.
     assert (In r rs1). { unfold set_eq in H1. destruct H1. unfold incl in H0. crush. }
     specialize (H r H0). crush.
  ++ auto.
}
rewrite H.
reflexivity.
Qed.

Theorem forall_WeakConfluence : WeakConfluence.
Proof.
  unfold WeakConfluence.
  intro t1.
  unfold Confluent.
  intro disjoint_rules_t1.
  intros sm t2.
  intro.
  apply equiv_equiv.
  specialize (disjoint_rules_of_transformation_permutation t1 t2 disjoint_rules_t1 H).
  intro disjoint_rules_t2.
  unfold TargetModel_equiv.
  simpl.
  intros.
  destruct H.
  split.
  - split.
    + unfold instantiatePattern.
      unfold matchPattern.
      intros.
      apply in_flat_map in H1. repeat destruct H1.
      apply in_flat_map in H2. repeat destruct H2.
      apply filter_In in H2. destruct H2.
      apply in_flat_map. exists x. split.
      * unfold allTuples.
        unfold maxArity.
        rewrite <- H.
        assumption.
      * apply in_flat_map.
        exists x0.
        split.
        -- apply filter_In.
           split.
           apply H0. assumption.
           assumption.
        -- assumption.
    +  unfold instantiatePattern.
      unfold matchPattern.
      intros.
      apply in_flat_map in H1. repeat destruct H1.
      apply in_flat_map in H2. repeat destruct H2.
      apply filter_In in H2. destruct H2.
      apply in_flat_map. exists x. split.
      * unfold allTuples.
        unfold maxArity.
        rewrite H.
        assumption.
      * apply in_flat_map.
        exists x0.
        split.
        -- apply filter_In.
           split.
           apply H0. assumption.
           assumption.
        -- assumption.
  - split.
    + unfold applyPattern.
      unfold matchPattern.
      intros.
      apply in_flat_map in H1. repeat destruct H1.
      apply in_flat_map in H2. repeat destruct H2.
      apply filter_In in H2. destruct H2.
      apply in_flat_map. exists x. split.
      * unfold allTuples.
        unfold maxArity.
        rewrite <- H.
        assumption.
      * apply in_flat_map.
        exists x0.
        split.
        -- apply filter_In.
           split.
           apply H0. assumption.
           assumption.
        -- unfold applyRuleOnPattern, applyIterationOnPattern in *.
           apply in_flat_map in H3. repeat destruct H3.
           apply in_flat_map.
           exists x1.
           split.
           ++ assumption.
           ++ apply in_flat_map in H5. repeat destruct H5.
              apply in_flat_map.
              exists x2.
              split.
              ** assumption.
              ** unfold applyElementOnPattern in *. 
                 assert (resolveIter t1 = resolveIter t2).
                  { apply resolveIter_eq. assumption. assumption. unfold Transformation_permutation . crush. }
                 destruct (evalOutputPatternElementExpr sm x x1 x2) eqn: eval_ope_ca.
                 *** rewrite H7 in H6.
                      auto.
                 *** (*rewrite H7 in H6.*)
                     exact H6.

+ unfold applyPattern.
      unfold matchPattern.
      intros.
      apply in_flat_map in H1. repeat destruct H1.
      apply in_flat_map in H2. repeat destruct H2.
      apply filter_In in H2. destruct H2.
      apply in_flat_map. exists x. split.
      * unfold allTuples.
        unfold maxArity.
        rewrite H.
        assumption.
      * apply in_flat_map.
        exists x0.
        split.
        -- apply filter_In.
           split.
           apply H0. assumption.
           assumption.
        -- unfold applyRuleOnPattern, applyIterationOnPattern in *.
           apply in_flat_map in H3. repeat destruct H3.
           apply in_flat_map.
           exists x1.
           split.
           ++ assumption.
           ++ apply in_flat_map in H5. repeat destruct H5.
              apply in_flat_map.
              exists x2.
              split.
              ** assumption.
              ** unfold applyElementOnPattern in *. 
assert ((resolveIter t1 = (resolveIter t2))).
{ apply resolveIter_eq. assumption. assumption. unfold Transformation_permutation . crush. }
destruct (evalOutputPatternElementExpr sm x x1 x2) eqn: eval_ope_ca.
*** rewrite <- H7 in H6.
    auto.
*** (*rewrite <- H7 in H6.*)
auto.
Qed.


(** M.T. Idea on define confluencec *)
(* Definition Confluence'' (t1: Transformation) :=
    forall (sm: SourceModel) (o o1: Order),
    TargetModel_equiv (execute t sm o) (execute t sm o1). *)


End Confluence.
