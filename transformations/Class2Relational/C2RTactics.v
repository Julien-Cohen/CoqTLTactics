
Require Import core.utils.Utils.

Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From core Require Tactics Certification.

(** ** Type correspondence *)

Lemma tables_come_from_classes a b c : 
  In (TableElement a) (instantiatePattern Class2Relational b [c]) ->
  exists d, c = ClassElement d.
Proof.
 destruct c ; simpl ; [ solve [eauto] | intro H ; exfalso ].
 simpl in H.
 destruct a0.
 destruct derived ; simpl in H ; auto.
 remove_or_false H.
 discriminate H.
Qed.

Lemma columns_come_from_attributes a b c : 
  In (ColumnElement a) (instantiatePattern Class2Relational b [c]) ->
  exists d, c = AttributeElement d.
Proof.
 destruct c ; simpl ; [intro H ; exfalso | solve[eauto] ].
 simpl in H.
 remove_or_false H.
 discriminate H.
Qed.





Ltac negb_inv H :=
  match type of H with
    negb (derived _) = true => 
      apply Bool.negb_true_iff in H
  end.
  



(** ** Destructors *)


(** *** Utilities on [allTuples] *)


Lemma allModelElements_allTuples e (cm:Model ClassMM): 
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

(* REMOVE-ME *)
Ltac unfold_traceElementOnPattern H :=
  match type of H with
  | traceElementOnPattern _ _ _ _ = return _ => 
      unfold traceElementOnPattern in H ; 
      OptionUtils.monadInv H
  end.

Ltac progress_in_traceElementOnPattern H := 
  Tactics.unfold_instantiateElementOnPattern H ; 
  Tactics.exploit_evaloutpat H.


Ltac unfold_toEData H :=
  unfold toEData in H ;
  simpl (unbox _) in H ;
  unfold get_E_data in H.

Ltac unfold_make_element H :=
  unfold ConcreteExpressions.makeElement in H ;
  unfold ConcreteExpressions.wrapElement in H ;
  unfold ConcreteExpressions.wrap in H ;
  unfold_toEData H ;
  unfold ClassMetamodel.get_E_data in H.

Ltac unfold_make_link H := 
  unfold ConcreteExpressions.makeLink in H ;
  unfold ConcreteExpressions.wrapLink in H ;
  unfold ConcreteExpressions.wrap in H;
  unfold_toEData H ;
  unfold ClassMetamodel.get_E_data in H.
