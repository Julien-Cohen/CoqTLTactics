(**
 CoqTL user theorem: Table_name_uniqueness
 Def: if all classes in the source model have unique name,
      then the target tables generated in the target model
      have unique name.
 **)

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



Theorem Table_name_uniqueness:
forall (cm : ClassModel) (rm : RelationalModel), 
(* transformation *) 
    rm = execute Class2Relational cm ->
(* precondition *)   
(forall (c1: Class) (c2: Class), 
    In (ClassMetamodel.toObject ClassClass c1) (allModelElements cm) -> 
    In (ClassMetamodel.toObject ClassClass c2) (allModelElements cm) -> 
    c1 <> c2 -> 
    class_name c1 <> class_name c2) ->
(* postcondition *)  
(forall (t1: Table) (t2: Table), 
    In (RelationalMetamodel.toObject TableClass t1) (allModelElements rm) -> 
    In (RelationalMetamodel.toObject TableClass t2) (allModelElements rm) -> 
    t1 <> t2 -> 
    table_name t1 <> table_name t2).
Proof.
    intros.
    subst rm.
    rewrite (tr_execute_in_elements Class2Relational) in H1, H2.
    destruct H1 as (? & (H1 & H11)).
    destruct H2 as (? & (H2 & H22)).

    repeat Tactics.show_singleton.

    simpl toObject in *.
    simpl ClassMetamodel.toObject in *.

    repeat Tactics.show_origin.


                specialize (H0 c0 c).
                apply allTuples_incl in H1.
                apply allTuples_incl in H2.
                unfold incl in H1, H2.
                specialize (H1 (ClassObject c)).
                specialize (H2 (ClassObject c0)).
                assert (I1 : In (ClassObject c) [ClassObject c]). 
                { left. reflexivity. }
                assert (I2 : In (ClassObject c0) [ClassObject c0]). 
                { left. reflexivity. }
                specialize (H0 (H2 I2)).
                specialize (H0 (H1 I1)).
                clear I1 I2 H1 H2.
                simpl in H11, H22.
                destruct H11 ; [ | contradiction].
                destruct H22 ; [ | contradiction].
                apply rel_invert in H1 ;
                apply rel_invert in H ; subst ; simpl in *.
                apply not_eq_sym ; apply H0.
                contradict H3.
                subst ; reflexivity.

Qed.

