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

Require Import transformations.Class2Relational_TUPLE_SP.Class2Relational_TUPLE_SP.
Require Import transformations.Class2Relational_TUPLE_SP.ClassMetamodel.
Require Import transformations.Class2Relational_TUPLE_SP.RelationalMetamodel.

(* From transformations.Class2Relational Require Tactics. *)

Theorem Column_name_uniqueness:
forall (cm : ClassModel) (rm : RelationalModel), 
    (* transformation *)
    rm = execute Class2Relational_TUPLE_SP cm ->
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


    (* (1) *)
    Tactics.chain_destruct_in_modelElements_execute IN1.
   
    (* (2) *)
    Tactics.progress_in_In_rules IN_RULE ; [ | ] ; 
    
    (* (3) *)
    Tactics.progress_in_ope IN_OP ; 

    (* (4) *)
    clear MATCH_GUARD ;

    (* (5.E) *)
    Tactics.exploit_evaloutpat IN1 ; 

    (* (6) *)
    clear IN_IT ;
    
    (* (7) *)
    exploit_in_allTuples IN_E ; [].



    (* (1) *)
    Tactics.chain_destruct_in_modelElements_execute IN2.
    
    (* (2) *)
    Tactics.progress_in_In_rules IN_RULE ; [ | ]; 
    
    (* (3) *)
    Tactics.progress_in_ope IN_OP ; 

    (* (4) *)
    clear  MATCH_GUARD ;
    
    (* (5) *)
    Tactics.exploit_evaloutpat IN2 ; 

    (* (6) *)
    clear IN_IT ;

    (* (7) *)
    exploit_in_allTuples IN_E1 ; [].
        
    simpl.

    eapply PRE ; eauto.
    
    contradict D. subst. reflexivity.

Qed.



  



