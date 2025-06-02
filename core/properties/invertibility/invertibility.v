From Stdlib 
  Require Import String EqNat List PeanoNat Lia FunctionalExtensionality.

From core 
  Require Import Semantics Syntax Model TransformationConfiguration Certification utils.Utils.

From core.modeling 
  Require Import ConcreteSyntax ModelingSemantics ModelingMetamodel ConcreteExpressions Parser.

From core.properties.injectivity 
  Require Import Injectivity.

From core.properties.surjectivity 
  Require Import surjectivity.


(*************************************************************)
(** * Surjectivity of CoqTL (Model)                          *)
(** * Using operational semantics                            *)
(*************************************************************)

Definition Left_Invertible {tc:TransformationConfiguration} (tr:Transformation) :=
    exists (tr_inv: Transformation (tc:= InverseTC tc)), forall (sm:SourceModel) (tm:TargetModel),
      (execute tr sm) = tm -> (execute tr_inv tm) = sm.


Definition Right_Invertible {tc:TransformationConfiguration} (tr:Transformation) :=
    exists (tr_inv: Transformation (tc:= InverseTC tc)), forall (sm:SourceModel) (tm:TargetModel),
      (execute tr_inv tm) = sm -> (execute tr sm) = tm.


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


Lemma right_invertible_surjective {tc:TransformationConfiguration} : 
  forall tr, Right_Invertible tr -> Surjectivity tr.
Proof.
 intro tr.
 unfold Right_Invertible.
 intros (tr_inv & H).
 unfold Surjectivity.
 intro tm.
 exists (execute tr_inv tm).
 apply H.
 reflexivity. 
Qed.


Corollary not_surjective_not_invertible :
   forall (tc:TransformationConfiguration) tr, 
      (~ Surjectivity tr) -> ~ Right_Invertible tr.
Proof.
  intros tc tr H ; contradict H ; apply right_invertible_surjective ; assumption.
Qed.

