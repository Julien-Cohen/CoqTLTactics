From Stdlib 
  Require Import String EqNat List PeanoNat Lia FunctionalExtensionality.

From core 
  Require Import Semantics Syntax Model TransformationConfiguration Certification utils.Utils.

From core.modeling 
  Require Import ConcreteSyntax ModelingSemantics ModelingMetamodel ConcreteExpressions Parser.

From core.properties.injectivity 
  Require Import Injectivity.



(*************************************************************)
(** * Left invertibility in CoqTL                            *)
(** * Using operational semantics                            *)
(*************************************************************)

Definition Left_Invertible {tc:TransformationConfiguration} (tr:Transformation) :=
    exists (tr_inv: Transformation (tc:= InverseTC tc)), forall (sm:SourceModel) (tm:TargetModel),
      (execute tr sm) = tm -> (execute tr_inv tm) = sm.


Lemma left_invertible_injective {tc:TransformationConfiguration} : 
  forall tr, Left_Invertible tr -> Injective_alt tr.
Proof.
  unfold Left_Invertible, Injective_alt.
  intros.
  destruct H as (tr_inv & H).

  assert (HSM1 : forall tm : TargetModel, execute tr sm1 = tm -> execute tr_inv tm = sm1) ; [ apply H | ].

  assert (HSM2 : forall tm : TargetModel, execute tr sm2 = tm -> execute tr_inv tm = sm2) ; [ apply H | ]. 

  specialize (HSM1 (execute tr sm1)).
  specialize (HSM2 (execute tr sm1)).
  rewrite <- HSM1 ; [ | reflexivity].
  apply HSM2 ; auto.
Qed.


Corollary not_injective_not_invertible :
   forall (tc:TransformationConfiguration) tr, 
      (~ Injective_alt tr) -> ~ Left_Invertible tr.
Proof.
  intros tc tr H ; contradict H ; apply left_invertible_injective ; assumption.
Qed.


Theorem not_invertible: 
  exists (tc:TransformationConfiguration) tr, ~ Left_Invertible tr.
Proof.
  exists   Moore2Mealy.Moore2MealyTransformationConfiguration.
  specialize Injectivity.exists_non_injective_alt.
  intros (tr & H).
  exists tr.
  apply not_injective_not_invertible ; assumption.
Qed.

