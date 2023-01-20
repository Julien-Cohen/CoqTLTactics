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

Require Import transformations.Class2Relational_TUPLE_SP.Class2Relational_TUPLE_SP.
Require Import transformations.Class2Relational_TUPLE_SP.ClassMetamodel.
Require Import transformations.Class2Relational_TUPLE_SP.RelationalMetamodel.

Theorem Attribute_name_preservation:
    forall (rm : RelationalModel) (cm: ClassModel),
        (* transformation *)
        rm = execute Class2Relational_TUPLE_SP cm ->
        (* postcondition *)  
        forall (a: Attribute_t) (c: Class_t),
        In (AttributeElement a) cm.(modelElements) ->
        In (ClassElement c) cm.(modelElements) ->
        derived a = false ->
        (getAttributeType a cm) = Some c ->
        exists (c: Column_t),
            In (ColumnElement c) rm.(modelElements) /\
            column_name c = attr_name a.
Proof.
    intros.
    exists (Build_Column_t (attr_id a) (attr_name a)).
    split.
    - rewrite H.
      rewrite (tr_execute_in_elements Class2Relational_TUPLE_SP).
      exists ([AttributeElement a; ClassElement c]).
      split.
      + apply allTuples_incl_length.
        * apply incl_singleton in H0.
          apply incl_singleton in H1.
          specialize (incl_app H0 H1).
          intro.
          simpl in H4. auto.
        * simpl. lia.
      + unfold instantiatePattern. unfold matchPattern. simpl.
        unfold ConcreteExpressions.makeGuard. simpl.
        rewrite H2. rewrite H3. simpl.
        specialize (beq_Class_refl c). intro.
        rewrite H4. simpl. left. reflexivity.
    - reflexivity.
Qed.
