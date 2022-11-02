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
Require Import transformations.Moore2Mealy.Moore2Mealy.
Require Import core.properties.injectivity.sampleMoore_injectivity.


(*************************************************************)
(** * Injectivity of CoqTL                                   *)
(*************************************************************)

Definition SourceModel_elem_eq {tc: TransformationConfiguration}  (m1 m2: SourceModel) : Prop := 
  set_eq (allModelElements m1) (allModelElements m2). 

Definition TargetModel_elem_eq {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  set_eq (allModelElements m1) (allModelElements m2). 

Definition Injectivity 
   (tr: Transformation) :=
forall sm1 sm2,
  TargetModel_elem_eq (execute tr sm1) (execute tr sm2) ->
    SourceModel_elem_eq sm1 sm2.  

Lemma Moore2Mealy_non_inj_contrapos:
exists sm1 sm2 : SourceModel,
  ~ SourceModel_elem_eq sm1 sm2 /\
  TargetModel_elem_eq (execute Moore2Mealy sm1) (execute Moore2Mealy sm2).
Proof.
  eexists Moore_m1.
  eexists Moore_m2.
  split.
  - unfold SourceModel_elem_eq.
    simpl.
    unfold set_eq.
    crush.
    remember (Moore.BuildState "S0" "1") as e1.
    remember (Moore.BuildState "S0" "0") as e2.
    unfold incl in H0.
    apply incl_cons_inv in H0.
    destruct H0.
    destruct H.
    + apply Moore_invert in H.
      crush.
    + destruct H.
  - unfold TargetModel_elem_eq.
    simpl.
    unfold set_eq.
    split; crush.
Qed.

Theorem Moore2Mealy_non_injective :
exists tr, Injectivity tr -> False.
Proof.
  eexists Moore2Mealy.
  unfold Injectivity.
  intro inj.
  specialize (Moore2Mealy_non_inj_contrapos) as inj_contrapos.
  crush.
Qed.