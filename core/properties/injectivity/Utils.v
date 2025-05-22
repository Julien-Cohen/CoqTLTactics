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


Definition SourceModel_elem_eq {tc: TransformationConfiguration}  (m1 m2: SourceModel) : Prop := 
  set_eq m1.(modelElements) m2.(modelElements). 

Definition TargetModel_elem_eq {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  set_eq m1.(modelElements) m2.(modelElements). 

Definition SourceModel_link_eq {tc: TransformationConfiguration}  (m1 m2: SourceModel) : Prop := 
  set_eq m1.(modelLinks) m2.(modelLinks). 

Definition TargetModel_link_eq {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  set_eq m1.(modelLinks) m2.(modelLinks). 

(** Lemmas *)

Lemma set_eq_Model_equiv MM : 
  forall (m1 m2 : Model MM)  , 
  set_eq m1.(modelElements) m2.(modelElements) -> 
  set_eq m1.(modelLinks) m2.(modelLinks) ->
   Model_equiv m1 m2.
Proof.
  intros.
  unfold Model_equiv.
  unfold Model_incl.
  split ; split ; intros.
  + apply H ; auto.
  + apply H0 ; auto.
  + apply H ; auto.
  + apply H0 ; auto.
Qed.  

Lemma Model_equiv_set_eq_elem MM : 
  forall (m1 m2 : Model MM)  , 
  Model_equiv m1 m2 ->
  set_eq m1.(modelElements) m2.(modelElements).
Proof.
  intros.
  destruct H as ((H1 & _) & (H3 & _)).
  split ; unfold incl ; intros ; auto.
Qed.  

Lemma Model_equiv_set_eq_link MM : 
  forall (m1 m2 : Model MM)  , 
  Model_equiv m1 m2 ->
  set_eq m1.(modelLinks) m2.(modelLinks).
Proof.
  intros.
  destruct H as ((_ & H2) & (_ & H4)).
  split ; unfold incl ; intros ; auto.
Qed.  
