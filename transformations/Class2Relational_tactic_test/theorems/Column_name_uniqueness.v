(**
 CoqTL user theorem: Column_name_uniqueness
 Def: if all attributes have unique names,
      then the generated columns have unique names.
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

Require core.TacticsBW.

Require Import transformations.Class2Relational_tactic_test.Class2Relational_tactic_test.
Require Import transformations.Class2Relational_tactic_test.ClassMetamodel.
Require Import transformations.Class2Relational_tactic_test.RelationalMetamodel.

(* From transformations.Class2Relational Require Tactics. *)

Theorem Column_name_uniqueness:
forall (cm : ClassModel) (rm : RelationalModel), 
    (* transformation *)
    rm = execute Class2Relational_tactic_test cm ->
    (* precondition *)
    (forall (at1: Attribute_t) (at2: Attribute_t),
        In (AttributeElement at1) cm.(modelElements) ->
        In (AttributeElement at2) cm.(modelElements) ->

        at1 <> at2 ->
        attr_name at1 <> attr_name at2) ->
    (* postcondition *)
    (forall (co1: Column_t) (co2: Column_t),
        In (ColumnElement co1) rm.(modelElements) ->
        In (ColumnElement co2) rm.(modelElements) ->

        co1 <> co2 ->
        column_name co1 <> column_name co2).
Proof.
    intros cm rm E PRE co1 co2 IN1 IN2 D.
    subst rm.

    TacticsBW.exploit_element_in_result IN1.
    TacticsBW.exploit_element_in_result IN2.
        
    simpl.

    eapply PRE ; eauto.
    
    contradict D. subst. reflexivity.

Qed.



  



