Require Import String.
Require Import List.

Require Import core.utils.Utils.
Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.


From transformations.Class2Relational 
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
  (* precondition *)  forall id name,
    In (AttributeElement {| Attribute_id:= id ; Attribute_derived := false ; Attribute_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (ColumnElement {| column_id := id; column_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros i n H.
  eapply C2RTactics.transform_element_fw ; [ exact H | ].
  compute.
  auto.
Qed.


Lemma transform_class_fw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
    In (ClassElement {| Class_id:= id ; Class_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (TableElement {| table_id := id; table_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros i n H.
  eapply C2RTactics.transform_element_fw ; [ exact H | ].
  compute.
  auto.
    (* Remark : exactly the same script as above. *)
Qed.


(** *** Backward Descriptions *)


Lemma transform_attribute_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
      In (ColumnElement {| column_id := id; column_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (AttributeElement {| Attribute_id:= id ; Attribute_derived := false ; Attribute_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst rm.
  intros i nm IN_ATTR.

  Tactics.exploit_element_in_result IN_ATTR ; [] ; 
  clear IN_ATTR.

  C2RTactics.negb_inv MATCH_GUARD.

  destruct t0 ; simpl in *. subst Attribute_derived. 
  assumption.
  
Qed.


Lemma transform_class_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
      In (TableElement {| table_id := id; table_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (ClassElement {| Class_id:= id ; Class_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst.
  intros i nm H.

  Tactics.exploit_element_in_result H ; []; 
  clear H.

  destruct t0 ; assumption.

Qed.
