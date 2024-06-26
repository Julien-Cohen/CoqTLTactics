(**
CoqTL user theorem: Attribute_name_preservation
Def: all non-derived attributes in the source model will create 
    a column in the target model with the same name
**)

Require Import String.
Require Import Lia.
Open Scope string_scope.

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
    destruct a ; simpl in H1 ; subst.

    (* Simple resolution (not the general case) *)
    Succeed solve [TacticsFW.transform_element_fw_tac].

    (* More general resolution *)
    TacticsFW.in_modelElements_singleton_fw_tac "Attribute2Column" "col" 0 H0 ; reflexivity. 
Qed.
