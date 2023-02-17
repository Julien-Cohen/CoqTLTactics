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

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From transformations.Class2Relational 
  Require C2RTactics Elements.


Theorem Column_name_uniqueness_third_proof:
forall (cm : ClassModel) (rm : RelationalModel), 
    (* transformation *)
    rm = execute Class2Relational cm ->
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
    destruct (Tactics.destruct_in_modelElements_execute_lem IN1) 
      as (r & sp & n & ope & IN_E & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & IN1'). 
   
    (* (2) *)
    Tactics.progress_in_In_rules IN_RULE ; [ | ] ; 
    
    (* (3) *)
    Tactics.progress_in_ope IN_OP ; 

    (* (4) *)
    Tactics.exploit_evalGuard MATCH_GUARD;
    
    (* (5) *)
    Tactics.exploit_evaloutpat IN1' ; 

    (* (6) *)
    clear IN_IT ;
    
    (* (7) *)
    Semantics.in_allTuples_auto ; [].

    (* (1) *)
    destruct (Tactics.destruct_in_modelElements_execute_lem IN2) 
      as (r & sp & n2 & ope & IN_E2 & IN_RULE & MATCH_GUARD2 & IN_IT & IN_OP & IN2'). 
    
    (* (2) *)
    Tactics.progress_in_In_rules IN_RULE ; [ | ]; 

    (* (3) *)
    Tactics.progress_in_ope IN_OP ;  
    
    (* (4) *)
    Tactics.exploit_evalGuard MATCH_GUARD2 ;
    
    (* (5) *)
    Tactics.exploit_evaloutpat IN2' ; 
    
    (* (6) *)
    clear IN_IT ;

    (* (7) *)
    Semantics.in_allTuples_auto ; [].
    
    simpl.

    eapply PRE ; eauto.
    
    contradict D ; subst ; reflexivity.
Qed.

 
(** An alternate proof based on simpler results. *)
Theorem Column_name_uniqueness_alt_proof :
forall (cm : ClassModel) (rm : RelationalModel), 
    (* transformation *)
    rm = execute Class2Relational cm ->
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
    
    destruct co1.
    eapply Elements.transform_attribute_bw in IN1 ; [ | reflexivity ].

    destruct co2.
    eapply Elements.transform_attribute_bw in IN2 ; [ | reflexivity ].
    
    simpl.
    
    specialize (PRE _ _ IN1 IN2) ; clear IN1 IN2 ; simpl in PRE.

    apply PRE ; clear PRE.
    contradict D ; PropUtils.inj D ; reflexivity.
Qed.


  



