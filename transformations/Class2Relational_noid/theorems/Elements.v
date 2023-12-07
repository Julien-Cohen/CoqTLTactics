Require Import String.
Require Import List.

Require Import core.utils.Utils.
Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require        core.TacticsBW.


From transformations.Class2Relational_noid 
  Require
  ClassModelProperties 
  RelationalModelProperties
  C2RTactics
  Class2Relational.


Import Class2Relational ClassMetamodel RelationalMetamodel.


(** Utilities on transformation of elements *)

(** *** Forward Descriptions *)


Lemma transform_attribute_fw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall name,
    In (AttributeElement {| Attribute_derived := false ; Attribute_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (ColumnElement {| Column_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros n H.
  TacticsFW.transform_element_fw_tac.
Qed.

(* Coming from previous work *)
Lemma transform_attribute_fw_no_tactic : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall name,
    In (AttributeElement {| Attribute_derived := false ; Attribute_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (ColumnElement {| Column_name := name |}) (rm.(modelElements)). 
Proof.
    intros.
    subst rm.
    simpl.
    unfold compute_trace, produced_elements. 
    rewrite map_flat_map. 
    apply in_flat_map.

    exists ([AttributeElement {| Attribute_derived := false; Attribute_name := name |}]).
    split.
    + apply Certification.allTuples_incl_length.
      * unfold incl.
        intros.
        apply in_inv in H.
        destruct H.
        -- rewrite <- H. assumption.
        -- contradiction H.
      * unfold Syntax.arity. simpl. auto.
    + simpl.
      left.
      reflexivity.
Qed.

Lemma transform_class_fw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall name,
    In (ClassElement {| Class_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (TableElement {| Table_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros n H.
  TacticsFW.transform_element_fw_tac.  
Qed.


(** *** Backward Descriptions *)


Lemma transform_attribute_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall name,
      In (ColumnElement {| Column_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (AttributeElement {| Attribute_derived := false ; Attribute_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst rm.
  intros nm IN_ATTR.

  TacticsBW.exploit_element_in_result IN_ATTR.

  C2RTactics.negb_inv MATCH_GUARD.

  destruct t0 ; simpl in *. subst Attribute_derived. 
  assumption.
  
Qed.


Lemma transform_class_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall name,
      In (TableElement {| Table_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (ClassElement {| Class_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst.
  intros nm H.

  TacticsBW.exploit_element_in_result H ; [].

  destruct t0 ; assumption.

Qed.
