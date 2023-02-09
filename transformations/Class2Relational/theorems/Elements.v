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




(** *** Utilities on transformation of elements *)


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
  simpl.
  apply C2RTactics.allModelElements_allTuples in H.
  revert H ; generalize (allTuples Class2Relational cm).
  induction l ; intro H ; [ solve [inversion H] | simpl ].
  apply List.in_or_app.
  simpl in H.
  destruct_or H ; [ left | right ].
  + subst.
    clear IHl.
    compute.
    left.
    reflexivity.
  + auto. 
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
  simpl.
  apply C2RTactics.allModelElements_allTuples in H.
  revert H ; generalize (allTuples Class2Relational cm).
  induction l ; intro H ; [ solve [inversion H] | simpl ].
  apply List.in_or_app.
  simpl in H.
  destruct_or H ; [ left | right ].
  + subst.
    clear IHl.
    compute.
    left.
    reflexivity.
  + auto. 

    (* Remark : exactly the same script as above. *)
Qed.





Lemma transform_attribute_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
      In (ColumnElement {| column_id := id; column_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (AttributeElement {| attr_id:= id ; derived := false ; attr_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst.
  intros i n H.

  (* (0) *)
  Tactics.chain_destruct_in_modelElements_execute H.
  clear IN_IT.

  (* (1) To progress in M and H, we need to know ope, and so we need to know r. Exploit IN_R. *)

  Tactics.progress_in_In_rules IN_M ; [ exfalso | ] ;

  (* (2) Now to progress in M or H we need to know ope. Exploit M (guard). *) 

  C2RTactics.progress_in_guard M ;


  (* (3) make the ouput-pattern-element appear *)
  C2RTactics.progress_in_ope IN_OP ;
  
  (* (4.E) make the matched element appear *)
  C2RTactics.progress_in_evalOutput H.

  apply Tactics.allModelElements_allTuples_back with (t:=Class2Relational).
  destruct a. simpl in D. subst derived.  exact IN_E.
  
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
  intros i n H.

  (* (0) *)
  Tactics.chain_destruct_in_modelElements_execute H.

  clear IN_IT.

  (* (1) *)
   Tactics.progress_in_In_rules IN_M ; [ | exfalso ] ; 
  
  (* (2) *)
  C2RTactics.progress_in_guard M ;

  (* (3) *)
  C2RTactics.progress_in_ope IN_OP ;
  
  (* (4.E) *)
  C2RTactics.progress_in_evalOutput H.
  
  apply Tactics.allModelElements_allTuples_back with (t:=Class2Relational).
  destruct x ; exact IN_E.

Qed.
