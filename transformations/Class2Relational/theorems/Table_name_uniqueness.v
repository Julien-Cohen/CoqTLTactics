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
(forall (c1: Class_t) (c2: Class_t), 
    In (ClassElement c1) cm.(modelElements) -> 
    In (ClassElement c2) cm.(modelElements) -> 
    c1 <> c2 -> 
    class_name c1 <> class_name c2) ->
(* postcondition *)  
(forall (t1: Table_t) (t2: Table_t), 
    In (TableElement t1) rm.(modelElements) -> 
    In (TableElement t2) rm.(modelElements) -> 
    t1 <> t2 -> 
    table_name t1 <> table_name t2).
Proof.
    intros cm rm E PRE t1 t2 IN1 IN2 D.
    subst rm.

    repeat Tactics.destruct_execute.

    repeat Tactics.show_singleton.

    repeat Tactics.show_origin.


                specialize (PRE c0 c).
                apply allTuples_incl in IN1.
                apply allTuples_incl in IN2.
                unfold incl in IN1, IN2.
                specialize (IN1 (ClassElement c)).
                specialize (IN2 (ClassElement c0)).
                assert (I1 : In (ClassElement c) [ClassElement c]). 
                { left. reflexivity. }
                assert (I2 : In (ClassElement c0) [ClassElement c0]). 
                { left. reflexivity. }
                specialize (PRE (IN2 I2)).
                specialize (PRE (IN1 I1)).
                clear I1 I2 IN1 IN2.
                simpl in H, H0.
                destruct_or H ; [ | contradiction].
                destruct_or H0 ; [ | contradiction].
                inversion H0 ;
                inversion H ; subst ; simpl in *.
                apply not_eq_sym ; apply PRE.
                contradict D.
                subst ; reflexivity.
Qed.

