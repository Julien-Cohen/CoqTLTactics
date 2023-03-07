Require Import String.
Require Import List.

Require Import core.utils.Utils.
Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.


From transformations.Class2Relational 
  Require
  ClassModelProperties 
  RelationalModelProperties
  C2RTactics
  Class2Relational.


Import Class2Relational ClassMetamodel RelationalMetamodel.




(** Utilities on transformation of elements *)

(** *** Forward Descriptions *)


Lemma transform_attribute_fw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
    In (AttributeElement {| attr_id:= id ; derived := false ; attr_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (ColumnElement {| column_id := id; column_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros i n H.
  eapply C2RTactics.transform_element_fw ; [ exact H | ].
  compute.
  auto.
Qed.


Lemma transform_class_fw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
    In (ClassElement {| class_id:= id ; class_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (TableElement {| table_id := id; table_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros i n H.
  eapply C2RTactics.transform_element_fw ; [ exact H | ].
  compute.
  auto.
    (* Remark : exactly the same script as above. *)
Qed.


(** *** Backward Descriptions *)

Lemma transform_attribute_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
      In (ColumnElement {| column_id := id; column_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (AttributeElement {| attr_id:= id ; derived := false ; attr_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst rm.
  intros i nm IN_ATTR.

  (* (1) *)
  destruct (Tactics.destruct_in_modelElements_execute_lem IN_ATTR) 
    as (r & sp & n & ope & IN_E & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & EV). 

  (* (2) *)
  Tactics.progress_in_In_rules IN_RULE ; [ exfalso | ] ;

  (* (3) make the ouput-pattern-element appear *)
  Tactics.progress_in_ope IN_OP ;

  (* (4) *) 
  (* needed here to get that derived = false *)
  Tactics.exploit_evalGuard MATCH_GUARD ; 
  
  (* (5.E) make the matched element appear *)
  Tactics.exploit_evaloutpat EV ;

  (* (6) *)
  (* not useful here *) 
  Tactics.exploit_in_it IN_IT ;

  (* (7) *)
  Semantics.exploit_in_allTuples IN_E.

  C2RTactics.negb_inv MATCH_GUARD.

  destruct t0 ; simpl in *. subst derived. 
  exact IN_E.
  
Qed.


Lemma transform_class_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
      In (TableElement {| table_id := id; table_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (ClassElement {| class_id:= id ; class_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst.
  intros i nm H.

  (* (1) *)
  destruct (Tactics.destruct_in_modelElements_execute_lem H) 
    as (r & sp & n & ope & IN_E & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & H').    

  (* (2) *)
  Tactics.progress_in_In_rules IN_RULE ; [ | exfalso ] ; 

  (* (3) *)
  Tactics.progress_in_ope IN_OP ;
  
  (* (4) *)
  (* not useful here *)
  Tactics.exploit_evalGuard MATCH_GUARD ; 

  (* (5.E) *)
  Tactics.exploit_evaloutpat H' ;

  (* (6) *)
  (* not useful here *) 
  Tactics.exploit_in_it IN_IT ;
  
  (* (7) *)
  Semantics.exploit_in_allTuples IN_E.
  
  destruct t0 ; exact IN_E.

Qed.
