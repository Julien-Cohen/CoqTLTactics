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

Theorem Class_name_preservation_fw:
    forall (rm : RelationalModel) (cm: ClassModel),
        (* transformation *)
        rm = execute Class2Relational cm ->
        (* postcondition *)  
        forall (c: Class_t),
        In (ClassElement c) cm.(modelElements) ->
        exists (t: Table_t),
            In (TableElement t) rm.(modelElements) /\ Table_name t = Class_name c.
Proof.
    intros.
    exists (Build_Table_t (Class_id c) (Class_name c)).
    split ; [ | reflexivity].
    subst rm.
    destruct c ; simpl in H0 ; subst.
    unfold ClassMetamodel.Class_id, ClassMetamodel.Class_name.

    simpl.
    unfold compute_trace. unfold produced_elements.
    rewrite ListUtils.map_flat_map.
    apply List.in_flat_map.
    match type of H0 with In ?E _ => exists ([E]) end.
    split.
    + apply <- SemanticsTools.in_allTuples_singleton. solve [auto].
    + simpl. auto.
Qed.
