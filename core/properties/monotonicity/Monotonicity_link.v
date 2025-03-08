
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
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.properties.monotonicity.Moore2Mealy_monotonicity_link_witness.
Require Import core.properties.monotonicity.sampleMoore_monotonicity_link.

(*************************************************************)
(** * Monotonicity of CoqTL  (link)                          *)
(** * Using operational semantics                            *)
(*************************************************************)

Definition SourceModel_link_incl {tc: TransformationConfiguration}  (m1 m2: SourceModel) : Prop := 
  incl (modelLinks m1) (modelLinks m2). 

Definition TargetModel_link_incl {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  incl (modelLinks m1) (modelLinks m2). 

Definition Monotonicity_link {tc: TransformationConfiguration} 
   (tr: Transformation) :=
forall sm1 sm2,
SourceModel_link_incl sm1 sm2 ->
TargetModel_link_incl (execute tr sm1) (execute tr sm2).  

Lemma Moore2Mealy_non_mono_contrapos_link:
  exists sm1 sm2 : SourceModel,
  SourceModel_link_incl sm1 sm2 /\
      ~ TargetModel_link_incl (execute Moore2Mealy sm1) (execute Moore2Mealy sm2).
Proof.
  exists Moore_m1.
  exists Moore_m2.
  split.
  - unfold SourceModel_link_incl.
    simpl.
    unfold incl.
    simpl.
    crush.
  - remember ((execute Moore2Mealy Moore_m2)) as t2.
    unfold execute in Heqt2.
    simpl in Heqt2.
    unfold applyTrLkOnModel in *.
    simpl in *.
    unfold TargetModel_link_incl.
    remember ((modelLinks t2)) as t2links.
    rewrite Heqt2 in Heqt2links.
    simpl in Heqt2links.
    rewrite Heqt2links.
    remember ((execute Moore2Mealy Moore_m1)) as t1.
    unfold execute in Heqt1.
    simpl in Heqt1.
    unfold applyTrLkOnModel in *.
    simpl in *.
    rewrite Heqt1.
    simpl.
    crush.
    apply incl_l_nil in H.
    crush.
Qed.


Lemma Moore2Mealy_non_mono_link : ~ (Monotonicity_link Moore2Mealy).
Proof.
  unfold Monotonicity_link.
  intro.
  specialize Moore2Mealy_non_mono_contrapos_link ; intro H2.
  crush.
Qed.

Theorem non_mono_link  :
  exists tr, ~ (Monotonicity_link tr).
Proof.
  exists Moore2Mealy.
  apply Moore2Mealy_non_mono_link.
Qed.



