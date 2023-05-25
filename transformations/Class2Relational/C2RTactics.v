
Require Import core.utils.Utils.

Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From core Require Tactics Certification.


Ltac negb_inv H :=
  match type of H with
    negb (derived _) = true => 
      apply Bool.negb_true_iff in H
  end.
  



(** ** Destructors *)


(** *** Utilities on [allTuples] *)


Lemma allModelElements_allTuples e (cm:Model ClassMM): 
  In e cm.(modelElements) ->
  In [e] (allTuples Class2Relational cm).
Proof. 
  intro.
  apply (Tactics.allModelElements_allTuples (tc:=C2RConfiguration));
    auto.
Qed.

Lemma in_allTuples_singleton :
  forall e t s, 
    In [e] (allTuples t s) ->
    In e s.(modelElements).
Proof.
  intros e t s IN.
  apply incl_singleton.
  eapply Certification.allTuples_incl.
  exact IN.
Qed.

(** *** January tactics *)


Ltac unfold_toEData H :=
  unfold toEData in H ;
  simpl (unbox _) in H ;
  unfold get_E_data in H.


(** *** Forward Descriptions *)

Lemma transform_element_fw cm e te :
  In e (modelElements cm) ->
  In te (elements_proj (traceTrOnPiece Class2Relational cm [e])) ->
  In te (modelElements (execute Class2Relational cm)).
Proof.
  intros IN1 IN2.
  eapply Tactics.transform_element_fw ; eauto.
Qed.

(** *** Tactics for Backward descriptions *)


Ltac exploit_element_in_result H :=
  match type of H with
  | In _ (modelElements (execute Class2Relational _)) =>
      
      let r := fresh "r" in
      let sp := fresh "sp" in
      let n := fresh "n" in
      let ope := fresh "ope" in
      let IN_E := fresh "IN_E" in
      let IN_RULE := fresh "IN_RULE" in
      let MATCH_GUARD := fresh "MATCH_GUARD" in
      let IN_IT := fresh "IN_IT" in
      let IN_OP := fresh "IN_OP" in
      let EV := fresh "EV" in
            
      (* (1) *)
      destruct (Tactics.destruct_in_modelElements_execute_lem H)
      as (r & sp & n & ope & IN_E & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & EV) ;
      
      (* (2) *)
      (* Case analysis on the rule that has matched. *)
      Tactics.progress_in_In_rules IN_RULE ;
      
      (* (3) *) 
      (* Make the ouput-pattern-element appear. *)
      Tactics.progress_in_In_outpat IN_OP ;
      
      (* (4) *) 
      (* Consider the fact that the guard was true. *)
      (* (needed here to get that derived = false) *)
      Tactics.exploit_evalGuard MATCH_GUARD ; 
      
      (* (5) *)
      (* Make the matched element appear *)
      Tactics.exploit_evaloutpat EV ;
      
      (* (6) *)
      Tactics.exploit_in_it IN_IT ;
      
      (* (7) *)
      Semantics.exploit_in_allTuples IN_E
  end. 
