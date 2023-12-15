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

Require usertools.TacticsFW.

Theorem Attribute_name_preservation_fw:
    forall (rm : RelationalModel) (cm: ClassModel),
        (* transformation *)
        rm = execute Class2Relational cm ->
        (* postcondition *)  
        forall (a: Attribute_t),
        In (AttributeElement a) cm.(modelElements) ->
        Attribute_derived a = false ->
        exists (c: Column_t),
            In (ColumnElement c) rm.(modelElements) /\
            Column_name c = Attribute_name a.
Proof.
    intros.
    exists (Build_Column_t (Attribute_id a) (Attribute_name a)).
    split ; [ | reflexivity].
    subst rm.
    TacticsFW.transform_element_fw_tac.
    destruct a ; simpl in H1 ; subst.
    TacticUtils.first_in_list.
Qed.

(* Without new tactics *)
Theorem Attribute_name_preservation_no_tactics:
    forall (rm : RelationalModel) (cm: ClassModel),
        (* transformation *)
        rm = execute Class2Relational cm ->
        (* postcondition *)  
        forall (a: Attribute_t),
        In (AttributeElement a) cm.(modelElements) ->
        Attribute_derived a = false ->
        exists (c: Column_t),
            In (ColumnElement c) rm.(modelElements) /\
            Column_name c = Attribute_name a.
Proof.
    intros.
    exists (Build_Column_t (Attribute_id a) (Attribute_name a)).
    split.
    - rewrite H.
      apply <- tr_execute_in_elements.
      exists ([AttributeElement a]).
      split.
      + unfold allTuples.
        setoid_rewrite  <- TupleUtils.tuples_up_to_n_incl_length. split.
        * unfold incl.
          intros.
          apply in_inv in H2.
          destruct H2.
          -- rewrite <- H2. assumption.
          -- contradiction.
        * unfold Syntax.arity. simpl. lia.
      + destruct a.
        simpl in H1.
        rewrite H1.
        simpl. 
        left.
        reflexivity.
    - reflexivity.
Qed.
