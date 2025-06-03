From Stdlib 
  Require Import String EqNat List PeanoNat Lia FunctionalExtensionality.

From core 
  Require Import Semantics Syntax Model TransformationConfiguration utils.Utils.

From core.modeling 
  Require Import ConcreteSyntax ModelingSemantics ModelingMetamodel ConcreteExpressions Parser.

From transformations.Moore2Mealy
  Require Import Moore Moore2Mealy.

From core.properties.injectivity
  Require Import Injectivity_elem Injectivity_link Utils.


(*************************************************************)
(** * Injectivity of CoqTL                                   *)
(** * Using operational semantics                            *)
(*************************************************************)


(** Injectivity (two definitions) *)

Definition Injective {tc: TransformationConfiguration} (tr: Transformation) :=
 forall sm1 sm2,
  Model_equiv (execute tr sm1) (execute tr sm2) ->
    Model_equiv sm1 sm2.  

Definition Injective_alt {tc: TransformationConfiguration} (tr: Transformation) :=
 forall sm1 sm2,
  (execute tr sm1) = (execute tr sm2) ->
     sm1  = sm2.  

(** Proof that CoqTL is not injective (Injective_alt) *)

From transformations.Moore2Mealy
  Require Import Moore Moore2Mealy.

From core.properties.injectivity 
  Require Import sampleMoore_injectivity_elem Utils.

Lemma Moore2Mealy_non_inj_contrapos_alt:
exists sm1 sm2 : SourceModel,
  ~  sm1 = sm2 /\
   execute Moore2Mealy sm1 = execute Moore2Mealy sm2.
Proof.
  exists Moore_m1.
  exists Moore_m2.
  split.
  - unfold Moore_m1, Moore_m2. intro. discriminate.
  - reflexivity.
Qed.


Lemma Moore2Mealy_non_injective_alt : ~ (Injective_alt Moore2Mealy).
Proof.
  unfold Injective_alt.
  intro inj.
  specialize (Moore2Mealy_non_inj_contrapos_alt) as inj_contrapos.
  crush.
Qed.

Lemma exists_non_injective_alt :
    exists tr, ~ (Injective_alt tr).
Proof.
  exists Moore2Mealy.
  apply Moore2Mealy_non_injective_alt.
Qed.

Theorem non_injective_alt  :
   ~ (forall tr, (Injective_alt tr)).
Proof.
  intro.
  specialize (exists_non_injective_alt).
  intro.
  destruct H0.
  specialize (H x).
  contradiction.
Qed.
