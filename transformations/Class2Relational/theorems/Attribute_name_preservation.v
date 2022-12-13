(**
CoqTL user theorem: Attribute_name_preservation
Def: all non-derived attributes in the source model will create 
    a column in the target model with the same name
**)

Require Import String.
Require Import Lia.
Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Semantics.
Require Import core.Certification.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.


Theorem Attribute_name_preservation:
    forall (rm : RelationalModel) (cm: ClassModel),
        (* transformation *)
        rm = execute Class2Relational cm ->
        (* postcondition *)  
        forall (a: Attribute_t),
        In (AttributeElement a) cm.(modelElements) ->
        derived a = false ->
        exists (c: Column_t),
            In (ColumnElement c) rm.(modelElements) /\
            column_name c = attr_name a.
Proof.
    intros.
    exists (Build_Column_t (attr_id a) (attr_name a)).
    split.
    - rewrite H.
      rewrite (tr_execute_in_elements Class2Relational).
      exists ([AttributeElement a]).
      split.
      + apply allTuples_incl_length.
        * apply incl_singleton ; assumption.
        * simpl. lia.
      + destruct a ; simpl in *.
        subst derived.
        simpl. 
        auto.
    - reflexivity.
Qed.
