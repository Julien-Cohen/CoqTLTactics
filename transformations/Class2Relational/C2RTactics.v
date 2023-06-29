
Require Import core.utils.Utils.

Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From core Require Tactics Certification.


Ltac negb_inv H :=
  match type of H with
    negb (Attribute_derived _) = true => 
      apply Bool.negb_true_iff in H
  end.
  



(** ** Destructors *)


(** *** Utilities on [allTuples] *)


Lemma allModelElements_allTuples e (cm:Model ClassMetamodel.MM): 
  In e cm.(modelElements) ->
  In [e] (allTuples Class2Relational cm).
Proof. 
  intro.
  apply (Tactics.allModelElements_allTuples (tc:=C2RConfiguration));
    auto.
Qed.

Lemma in_allTuples_singleton :
  forall e t s, 
    In [e] (allTuples t s) ->
    In e s.(modelElements).
Proof.
  intros e t s IN.
  apply incl_singleton.
  eapply Certification.allTuples_incl.
  exact IN.
Qed.

(** *** January tactics *)


Ltac unfold_toEData H :=
  unfold toEData in H ;
  simpl (unbox _) in H ;
  unfold get_E_data in H.




