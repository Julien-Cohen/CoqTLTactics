From Stdlib 
  Require Import String EqNat List PeanoNat Lia FunctionalExtensionality.

From core 
  Require Import Semantics Syntax Model TransformationConfiguration utils.Utils.

From core.modeling 
  Require Import ConcreteSyntax ModelingSemantics ModelingMetamodel ConcreteExpressions Parser.

From transformations.Moore2Mealy
  Require Import Moore Moore2Mealy.

From core.properties.injectivity 
  Require Import sampleMoore_injectivity_elem Utils.

(*************************************************************)
(** * Injectivity of CoqTL (Element)                         *)
(** * Using operational semantics                            *)
(*************************************************************)

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

Lemma exists_non_injective_elem :
    exists tr, ~ (Injectivity_elem tr).
Proof.
  exists Moore2Mealy.
  apply Moore2Mealy_non_injective_elem.
Qed.

Theorem non_injective_elem  :
   ~ (forall tr, (Injectivity_elem tr)).
Proof.
  intro.
  specialize (exists_non_injective_elem).
  intro.
  destruct H0.
  specialize (H x).
  contradiction.
Qed.


(** Other definition,
   based on = (eq) instead of equiv (TargetModel_elem_eq, SourceModel_elem_eq or Model_eq) *)

Definition Injectivity_elem_alt {tc: TransformationConfiguration}
   (tr: Transformation) :=
forall sm1 sm2,
   (execute tr sm1).(modelElements) = (execute tr sm2).(modelElements) ->
    sm1.(modelElements) = sm2.(modelElements).  

Lemma Moore2Mealy_non_inj_elem_contrapos_alt:
exists sm1 sm2 : SourceModel,
  ~  sm1.(modelElements) = sm2.(modelElements) /\
   (execute Moore2Mealy sm1).(modelElements) = (execute Moore2Mealy sm2).(modelElements).
Proof.
  exists Moore_m1.
  exists Moore_m2.
  split.
  - simpl.
    congruence.
  - reflexivity.
Qed.

Lemma Moore2Mealy_non_injective_elem_alt : ~ (Injectivity_elem_alt Moore2Mealy).
Proof.
  unfold Injectivity_elem_alt.
  intro inj.
  specialize (Moore2Mealy_non_inj_elem_contrapos_alt) as inj_contrapos.
  crush.
Qed.

Lemma exists_non_injective_elem_alt :
    exists tr, ~ (Injectivity_elem_alt tr).
Proof.
  exists Moore2Mealy.
  apply Moore2Mealy_non_injective_elem_alt.
Qed.

Theorem non_injective_elem_alt  :
   ~ (forall tr, (Injectivity_elem_alt tr)).
Proof.
  intro.
  specialize (exists_non_injective_elem_alt).
  intro.
  destruct H0.
  specialize (H x).
  contradiction.
Qed.


