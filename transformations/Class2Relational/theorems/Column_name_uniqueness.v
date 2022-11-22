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
    (forall (at1: Attribute_t) (at2: Attribute_t) (cl: Class_t) (*(ats: list Attribute_t)*),
        In (ClassMetamodel.lift_EKind Attribute_K at1) (allModelElements cm) ->
        In (ClassMetamodel.lift_EKind Attribute_K at2) (allModelElements cm) ->
        In (ClassMetamodel.lift_EKind Class_K cl) (allModelElements cm) ->
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

    repeat Tactics.destruct_execute.
   
    repeat Tactics.show_singleton.
    
    simpl RelationalMetamodel.toObject in *.
    simpl ClassMetamodel.lift_EKind in *.
    repeat Tactics.show_origin. 

          specialize (PRE a a0 c).
 
            apply allTuples_incl in IN1.
            apply allTuples_incl in IN2.
            apply allTuples_incl in IN3.
            unfold incl in IN1, IN2, IN3.
            specialize (IN1 (AttributeElement a)).
            specialize (IN2 (AttributeElement a0)).
            specialize (IN3 (ClassElement c)).


            assert (I4 : In (AttributeElement a) (allModelElements cm)).
            { apply IN1. simpl. auto. }

            clear IN1.

            assert (I5 : In (AttributeElement a0) (allModelElements cm)).       
            { apply IN2. simpl. auto. }

            clear IN2.

            assert (I6 : In (ClassElement c) (allModelElements cm)).
            { apply IN3. simpl. auto. }

            clear IN3.



            specialize (PRE I4 I5 I6). clear I4 I5 I6.

            simpl in H.

            destruct a, a0 ; [] ; simpl in *.
            replace derived with false in *  ; [ | solve [destruct derived ; auto] ].
            replace derived0 with false in * ; [ | solve [destruct derived0 ; auto] ].

            simpl in H, H0.

            destruct_or H1 ; [ | contradiction].
            destruct_or H0 ; [ | contradiction].
            destruct_or H  ; [ | contradiction].

            apply rel_invert in H1.
            apply rel_invert in H0.
            apply rel_invert in H.
            subst. simpl.

            apply PRE.
            contradict D.
            injection D ; clear D ; intros ; subst.
            reflexivity.
Qed.

 


  



