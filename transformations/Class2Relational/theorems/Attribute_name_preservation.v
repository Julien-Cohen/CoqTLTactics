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
        In (ClassMetamodel.lift_EKind Attribute_K a) cm.(modelElements) ->
        derived a = false ->
        exists (c: Column_t),
            In (RelationalMetamodel.lift_EKind Column_K c) rm.(modelElements) /\
            column_name c = attr_name a.
Proof.
    intros.
    exists (Build_Column_t (attr_id a) (attr_name a)).
    split.
    - rewrite H.
      rewrite (tr_execute_in_elements Class2Relational).
      exists ([ClassMetamodel.lift_EKind Attribute_K a]).
      split.
      + apply allTuples_incl_length.
        * unfold incl.
          intros.
          apply in_inv in H2.
          destruct H2.
          -- rewrite <- H2. assumption.
          -- contradiction.
        * simpl. lia.
      + destruct a.
        simpl in H1.
        rewrite H1.
        simpl. 
        left.
        reflexivity.
    - reflexivity.
Qed.
