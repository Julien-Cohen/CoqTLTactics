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
        In (AttributeElement at1) cm.(modelElements) ->
        In (AttributeElement at2) cm.(modelElements) ->
        In (ClassElement cl) cm.(modelElements) ->
(*        getClassAttributes cl cm = Some ats ->
        In at1 ats ->
        In at2 ats ->*)
        at1 <> at2 ->
        attr_name at1 <> attr_name at2) ->
    (* postcondition *)
    (forall (co1: Column_t) (co2: Column_t) (ta: Table_t) (*(cos: list Column)*),
        In (ColumnElement co1) rm.(modelElements) ->
        In (ColumnElement co2) rm.(modelElements) ->
        In (TableElement ta) rm.(modelElements) ->
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
    

    repeat Tactics.show_origin. 
    
    Tactics.in_singleton_allTuples IN1.
    Tactics.in_singleton_allTuples IN2.
    Tactics.in_singleton_allTuples IN3.

           specialize (PRE a a0 c IN1 IN2 IN3). clear IN1 IN2 IN3.

            simpl in H.

            destruct a, a0 ; [] ; simpl in *.
            replace derived with false in *  ; [ | solve [destruct derived ; auto] ].
            replace derived0 with false in * ; [ | solve [destruct derived0 ; auto] ].

            simpl in H, H0.

            remove_or_false H.
            remove_or_false H0.
            remove_or_false H1.

            inversion H1. 
            inversion H0. 
            inversion H. 
            subst. simpl.

            apply PRE.
            contradict D.
            injection D ; clear D ; intros ; subst.
            reflexivity.
Qed.

 


  



