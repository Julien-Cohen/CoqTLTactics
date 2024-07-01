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

    (* Simple resolution (not the general case) *)
    Succeed solve [TacticsFW.transform_element_fw_tac].

    (* More general resolution *)
    TacticsFW.in_modelElements_singleton_fw_tac "Class2Table" "tab" 0 H0 ; reflexivity. 
Qed.
