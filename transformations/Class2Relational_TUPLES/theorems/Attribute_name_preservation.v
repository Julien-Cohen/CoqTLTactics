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
Open Scope string_scope.

Require Import transformations.Class2Relational_TUPLES.Class2Relational_TUPLES.
Require Import transformations.Class2Relational_TUPLES.ClassMetamodel.
Require Import transformations.Class2Relational_TUPLES.RelationalMetamodel.

Require TacticsFW.

Theorem Attribute_name_preservation:
    forall (rm : RelationalModel) (cm: ClassModel),
        (* transformation *)
        rm = execute Class2Relational_TUPLES cm ->
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
  subst rm.
  eexists.
  
  split.
  + TacticsFW.in_modelElements_pair_fw_tac "Attribute2Column" "col" 0 H0 H1 ; try reflexivity ; [].
    unfold ConcreteExpressions.makeGuard.
    unfold ConcreteExpressions.wrap.
    
    simpl.
    rewrite H2.
    simpl.
    rewrite H3.
    simpl.
    apply internal_Class_t_dec_lb ; auto.
  + reflexivity.
Qed.
