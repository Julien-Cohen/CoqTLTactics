
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
Require        core.Certification.
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.properties.surjectivity.Moore2Mealy_surjectivity_model_witness.
Require Import core.properties.surjectivity.sampleMealy_surjectivity_model.

(*************************************************************)
(** * Surjectivity of CoqTL (Model)                          *)
(** * Using operational semantics                            *)
(*************************************************************)

Definition Surjectivity {tc:TransformationConfiguration} (tr:Transformation) :=
    forall (tm: TargetModel), exists (sm: SourceModel), (execute tr sm) = tm.



Lemma Moore2Mealy_non_surj_contrapos : 
    exists (tm: TargetModel), forall (sm: SourceModel), ~ ((execute Moore2Mealy sm) = tm).
Proof.
exists Mealy_model.
intros.
destruct sm as (models & links).
induction models.
+ (* modelElements = nil *)
  unfold Moore2Mealy.
  unfold execute.
  simpl.
  unfold Mealy_model.
  crush.
+ (* modelElements <> nil *)
  destruct a.
  ++ (* element is a State *)
     unfold Moore2Mealy.
     unfold execute.
     simpl.
     unfold Mealy_model.
     unfold convert_state.
     crush.
  ++ (* element is a Transition *)
     unfold Moore2Mealy.
     unfold execute.
     simpl.
     unfold Mealy_model.
     unfold convert_state.
     crush.
Qed.

Lemma Moore2Mealy_not_Surjectivity : ~ (Surjectivity Moore2Mealy).
Proof.
    unfold Surjectivity.
    intro.
    specialize Moore2Mealy_non_surj_contrapos.
    intro.
    destruct H0.
    specialize (H x).
    destruct H.
    specialize (H0 x0).
    crush.
Qed.

Lemma exists_not_Surjectivity : 
   exists (tr:Transformation), ~ Surjectivity tr.
Proof.
exists Moore2Mealy.
apply Moore2Mealy_not_Surjectivity.
Qed.


Theorem not_forall_Surjectivity :
    ~ (forall (tr:Transformation), Surjectivity tr).
Proof.
intro.
specialize (exists_not_Surjectivity).
intro.
destruct H0.
specialize (H x).
contradiction.
Qed.  


(** Alternate definition of surjectivity based on Model_equiv *)

Definition Surjectivity_alt {tc:TransformationConfiguration} (tr:Transformation) :=
    forall (tm: TargetModel), exists (sm: SourceModel), Model_equiv (execute tr sm) tm.

(** The alternate definition is weaker than the inital one. *)
Lemma surjectivity_order : 
  forall tc t, Surjectivity (tc:=tc) t -> Surjectivity_alt t.
Proof.
 unfold Surjectivity, Surjectivity_alt ; intros.
 specialize (H tm).
 destruct H.
  exists x. rewrite H. auto. apply Model_equiv_refl.
Qed.

Lemma surjectivity_contrap : 
  forall tc t, ~Surjectivity_alt (tc:=tc) t -> ~Surjectivity t.
Proof.
    intros.
    contradict H.
    apply surjectivity_order. assumption.
Qed.
