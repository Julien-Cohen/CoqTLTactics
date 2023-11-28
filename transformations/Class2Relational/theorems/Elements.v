Require Import String.
Require Import List.

Require Import core.utils.Utils.
Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require        core.TacticsBW.


From transformations.Class2Relational 
  Require
  ClassModelProperties 
  RelationalModelProperties
  C2RTactics
  Class2Relational.


Import Class2Relational ClassMetamodel RelationalMetamodel.


Notation transform_element_fw := 
  (TacticsFW.transform_element_fw  (tc := Class2Relational.C2RConfiguration)).


(** Utilities on transformation of elements *)

(** *** Forward Descriptions *)


Lemma transform_attribute_fw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
    In (AttributeElement {| Attribute_id:= id ; Attribute_derived := false ; Attribute_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (ColumnElement {| Column_id := id; Column_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros i n H.
  eapply transform_element_fw ; eauto.
  compute ; auto.
Qed.


Lemma transform_class_fw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
    In (ClassElement {| Class_id:= id ; Class_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (TableElement {| Table_id := id; Table_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros i n H.
  eapply transform_element_fw ; eauto.
  compute ; auto.
Qed.


(** *** Backward Descriptions *)


Lemma transform_attribute_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
      In (ColumnElement {| Column_id := id; Column_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (AttributeElement {| Attribute_id:= id ; Attribute_derived := false ; Attribute_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst rm.
  intros i nm IN_ATTR.

  TacticsBW.exploit_element_in_result IN_ATTR.

  C2RTactics.negb_inv MATCH_GUARD.

  destruct t0 ; simpl in *. subst Attribute_derived. 
  assumption.
  
Qed.


Lemma transform_class_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
      In (TableElement {| Table_id := id; Table_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (ClassElement {| Class_id:= id ; Class_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst.
  intros i nm H.

  TacticsBW.exploit_element_in_result H ; [].

  destruct t0 ; assumption.

Qed.
