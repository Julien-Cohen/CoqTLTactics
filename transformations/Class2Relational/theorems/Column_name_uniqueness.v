(**
 CoqTL user theorem: Column_name_uniqueness
 Def: if all attributes of the same class have unique names,
      then the generated columns of the same table
      have unique names.
 **)

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import String.
Require Import core.utils.Utils.

(*Require Import core.Semantics.
Require Import core.Certification.*)
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From transformations.Class2Relational Require Tactics.

Theorem Column_name_uniqueness:
forall (cm : ClassModel) (rm : RelationalModel), 
    (* transformation *)
    rm = execute Class2Relational cm ->
    (* precondition *)
    (forall (at1: Attribute) (at2: Attribute) (cl: Class) (*(ats: list Attribute)*),
        In (ClassMetamodel.toObject AttributeClass at1) (allModelElements cm) ->
        In (ClassMetamodel.toObject AttributeClass at2) (allModelElements cm) ->
        In (ClassMetamodel.toObject ClassClass cl) (allModelElements cm) ->
(*        getClassAttributes cl cm = Some ats ->
        In at1 ats ->
        In at2 ats ->*)
        at1 <> at2 ->
        attr_name at1 <> attr_name at2) ->
    (* postcondition *)
    (forall (co1: Column) (co2: Column) (ta: Table) (*(cos: list Column)*),
        In (RelationalMetamodel.toObject ColumnClass co1) (allModelElements rm) ->
        In (RelationalMetamodel.toObject ColumnClass co2) (allModelElements rm) ->
        In (RelationalMetamodel.toObject TableClass ta) (allModelElements rm) ->
(*        getTableColumns ta rm = Some cos ->
        In co1 cos ->
        In co2 cos ->*)
        co1 <> co2 ->
        column_name co1 <> column_name co2).
Proof.
    intros cm rm E PRE co1 co2 ta IN1 IN2 IN3 D.
    subst rm.

    rewrite (tr_execute_in_elements Class2Relational) in IN1, IN2, IN3.
    destruct IN1 as (? & (H1 & H11)).
    destruct IN2 as (? & (H2 & H22)).
    destruct IN3 as (? & (H3 & H33)).


    repeat Tactics.show_singleton.
    
    simpl RelationalMetamodel.toObject in *.
    simpl ClassMetamodel.toObject in *.
    repeat Tactics.show_origin. 

          specialize (PRE a a0 c).
 
            apply allTuples_incl in H1.
            apply allTuples_incl in H2.
            apply allTuples_incl in H3.
            unfold incl in H1, H2, H3.
            specialize (H1 (AttributeObject a)).
            specialize (H2 (AttributeObject a0)).
            specialize (H3 (ClassObject c)).


            assert (I4 : In (AttributeObject a) (allModelElements cm)).
            { apply H1. simpl. auto. }

            clear H1.

            assert (I5 : In (AttributeObject a0) (allModelElements cm)).       
            { apply H2. simpl. auto. }

            clear H2.

            assert (I6 : In (ClassObject c) (allModelElements cm)).
            { apply H3. simpl. auto. }

            clear H3.



            specialize (PRE I4 I5 I6). clear I4 I5 I6.

            simpl in H11.

            destruct a, a0 ; [] ; simpl in *.
            replace derived with false in *  ; [ | solve [destruct derived ; auto] ].
            replace derived0 with false in * ; [ | solve [destruct derived0 ; auto] ].

            simpl in H11, H22.

            destruct H33 as [ H33 | H33] ; [ | contradiction].
            destruct H22 as [ H22 | H22] ; [ | contradiction].
            destruct H11 as [ H11 | H11] ; [ | contradiction].

            apply rel_invert in H11.
            apply rel_invert in H22.
            apply rel_invert in H33.
            subst. simpl.

            apply PRE.
            contradict D.
            injection D ; clear D ; intros ; subst.
            reflexivity.
Qed.

 


  



