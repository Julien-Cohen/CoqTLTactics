From Stdlib 
  Require Import String EqNat List PeanoNat Lia FunctionalExtensionality.

From core 
  Require Import Semantics Syntax Model TransformationConfiguration Certification utils.Utils.

From core.modeling 
  Require Import ConcreteSyntax ModelingSemantics ModelingMetamodel ConcreteExpressions Parser.


From core.properties.surjectivity 
  Require Import surjectivity.


(*************************************************************)
(** * Right invertibility in CoqTL                           *)
(** * Using operational semantics                            *)
(*************************************************************)

Definition Right_Invertible {tc:TransformationConfiguration} (tr:Transformation) :=
    exists (tr_inv: Transformation (tc:= InverseTC tc)), forall (sm:SourceModel) (tm:TargetModel),
      (execute tr_inv tm) = sm -> (execute tr sm) = tm.


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

