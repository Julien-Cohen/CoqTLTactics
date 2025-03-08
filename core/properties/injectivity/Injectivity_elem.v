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
Require Import core.properties.injectivity.sampleMoore_injectivity_elem.

(*************************************************************)
(** * Injectivity of CoqTL (Element)                         *)
(** * Using operational semantics                            *)
(*************************************************************)

Definition SourceModel_elem_eq {tc: TransformationConfiguration}  (m1 m2: SourceModel) : Prop := 
  set_eq m1.(modelElements) m2.(modelElements). 

Definition TargetModel_elem_eq {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  set_eq m1.(modelElements) m2.(modelElements). 

Definition Injectivity_elem {tc: TransformationConfiguration}
   (tr: Transformation) :=
forall sm1 sm2,
  TargetModel_elem_eq (execute tr sm1) (execute tr sm2) ->
    SourceModel_elem_eq sm1 sm2.  

Lemma Moore2Mealy_non_inj_elem_contrapos:
exists sm1 sm2 : SourceModel,
  ~ SourceModel_elem_eq sm1 sm2 /\
  TargetModel_elem_eq (execute Moore2Mealy sm1) (execute Moore2Mealy sm2).
Proof.
  exists Moore_m1.
  exists Moore_m2.
  split.
  - unfold SourceModel_elem_eq.
    simpl.
    unfold set_eq.
    crush.
    remember (Moore.Build_State_t (Id.Id "S0") "1") as e1.
    remember (Moore.Build_State_t (Id.Id "S0") "0") as e2.
    unfold incl in H0.
    apply incl_cons_inv in H0.
    destruct H0.
    destruct H.
    + injection H.
      crush.
    + destruct H.
  - unfold TargetModel_elem_eq.
    simpl.
    unfold set_eq.
    split; crush.
Qed.

Lemma Moore2Mealy_non_injective_elem : ~ (Injectivity_elem Moore2Mealy).
Proof.
  unfold Injectivity_elem.
  intro inj.
  specialize (Moore2Mealy_non_inj_elem_contrapos) as inj_contrapos.
  crush.
Qed.

Theorem non_injective_elem :
    exists tr, ~ (Injectivity_elem tr).
Proof.
  exists Moore2Mealy.
  apply Moore2Mealy_non_injective_elem.
Qed.
