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

Require Import transformations.Moore2Mealy.Moore.
Require Import core.properties.injectivity.Moore2Mealy_injectivity_link_witness.
Require Import core.properties.injectivity.sampleMoore_injectivity_link.
Require Import core.properties.injectivity.Utils.

(*************************************************************)
(** * Injectivity of CoqTL (Link)                            *)
(** * Using operational semantics                            *)
(*************************************************************)


Definition Injectivity_link {tc: TransformationConfiguration}
   (tr: Transformation) :=
forall sm1 sm2,
  TargetModel_link_eq (execute tr sm1) (execute tr sm2) ->
    SourceModel_link_eq sm1 sm2.  

Lemma Moore2Mealy_non_inj_link_contrapos:
exists sm1 sm2 : SourceModel,
  ~ SourceModel_link_eq sm1 sm2 /\
  TargetModel_link_eq (execute Moore2Mealy sm1) (execute Moore2Mealy sm2).
Proof.
  exists Moore_m1.
  exists Moore_m2.
  split.
  - unfold SourceModel_link_eq.
    simpl.
    unfold set_eq.
    crush.
    unfold incl in H0.
    apply incl_cons_inv in H0.
    destruct H0.
    destruct H.
    + injection H.
      crush.
    + destruct H.
      crush.
      simpl in H.
      contradiction.
  - unfold TargetModel_link_eq.
    simpl.
    unfold set_eq.
    split; crush.
Qed.

Lemma Moore2Mealy_non_injective_link : ~ (Injectivity_link Moore2Mealy).
Proof.
  unfold Injectivity_link.
  intro inj.
  specialize (Moore2Mealy_non_inj_link_contrapos) as inj_contrapos.
  crush.
Qed.

Theorem exists_non_injective_link :
    exists tr, ~ (Injectivity_link tr).
Proof.
  exists Moore2Mealy.
  apply Moore2Mealy_non_injective_link.
Qed.


Theorem non_injective_link  :
   ~ (forall tr, (Injectivity_link tr)).
Proof.
  intro.
  specialize (exists_non_injective_link).
  intro.
  destruct H0.
  specialize (H x).
  contradiction.
Qed.