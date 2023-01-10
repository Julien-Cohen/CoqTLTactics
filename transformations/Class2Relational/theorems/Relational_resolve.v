Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.

Require Import core.utils.Utils.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From transformations.Class2Relational 
  Require ClassMetamodelProperties RelationalMetamodelProperties.

From transformations.Class2Relational Require Tactics.


(* FIXME : move-me *)
Ltac duplicate H1 H2 := remember H1 as H2 eqn: TMP ; clear TMP.


(** *** Utilities on transformation of elements *)

(* FIXME : move-me *)
(* NOT USED *)
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
  apply Tactics.allModelElements_allTuples in H.
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

(* FIXME : move-me *)
(* NOT USED *)
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
  simpl in H.
  apply Tactics.allModelElements_allTuples_back with (t:=Class2Relational).
  revert H ; generalize (allTuples Class2Relational cm).
  induction l ; intro H ; [ solve [inversion H] | simpl ].
  simpl in H.
  apply List.in_app_or in H.

  destruct_or H ; [ left | right ].
  + Tactics.show_singleton.
    Tactics.show_origin.
    f_equal.
    f_equal.
    destruct a.
    destruct derived ; compute in H.
    - contradiction.
    - remove_or_false H.
      injection H ; intros ;subst ; clear H.
      reflexivity.
  + auto.
Qed.

  
(** *** Result *)

From transformations.Class2Relational Require TraceUtils.

Theorem Relational_Column_Reference_definedness:
forall (cm : ClassModel) (rm : RelationalModel), 

  (* transformation *) rm = execute Class2Relational cm ->

  (* precondition *)  (forall (att : Attribute_t),
      In (AttributeElement att) cm.(modelElements) ->
      exists (r:Class_t), 
        getAttributeType att cm = Some r 
        /\ In (ClassElement r) cm.(modelElements) (* well-formed *) ) ->  

    (* postcondition *)  forall (col: Column_t),
      In (ColumnElement col) rm.(modelElements) ->
      exists r', getColumnReference col rm =Some r'. 

Proof. 
  intros cm rm E PRE.  intros col I1.
  subst rm.
  Tactics.destruct_execute.
  Tactics.show_singleton.
  Tactics.show_origin.
  repeat Tactics.destruct_any.

  clear IN_I. 
  
  apply Tactics.allModelElements_allTuples_back in IN_E.
  
  specialize (PRE _ IN_E).
  destruct PRE as (t & (PRE1 & PRE2)).
 
  unfold getColumnReference.

  unfold execute.  simpl. 

  set (z:=r).

  Tactics.destruct_In_two ; [ exfalso | ] ; 
   simpl in IN_OP ; remove_or_false IN_OP ; subst ope ; [ discriminate I1 | Tactics.inj I1]. 
  
  clear n. 
  simpl in M.
  
  Tactics.deduce_element_kind_from_guard. (* M *)
 
  destruct a0 ; simpl in *. (* derived a0 = false *)
  subst derived ; simpl in *. 

  duplicate PRE1 G1.
  apply ClassMetamodelProperties.get_in in PRE1.

  specialize (TraceUtils.in_maybeResolve_trace_2 t cm PRE2 ) ; intros (R & I).


  eapply RelationalMetamodelProperties.in_get_2_right 
    with (x:= {| table_id :=t.(class_id) ;  
                table_name := t.(class_name) |}) . 

    apply in_flat_map.
    exists ([AttributeElement {|
                attr_id := attr_id;
                derived := false;
                attr_name := attr_name
              |}]).
    split.
    { apply Tactics.allModelElements_allTuples. exact IN_E. }
    {

      unfold applyPattern.
    apply in_flat_map.
    exists z.
  
    split.
    { subst z. simpl. auto. }
    { 
      apply tr_applyRuleOnPattern_in ; simpl.
      exists 0.
      split ; [ solve [auto] | ].
      apply tr_applyIterationOnPattern_in.
      eexists  ; split ; [ solve [subst z ; simpl ; auto] | ].
      erewrite tr_applyElementOnPattern_leaf ; simpl.
      2:{ compute. reflexivity. }

      rewrite <- app_nil_end. 
      simpl.
      
      unfold Parser.parseOutputPatternLink ; simpl.
      unfold ConcreteExpressions.makeLink ; simpl.
      unfold ConcreteExpressions.wrapLink ; simpl.
      unfold getAttributeTypeElement.
      rewrite G1. simpl.

      unfold ModelingSemantics.maybeResolve.
      unfold singleton.
      rewrite R. 

      simpl. left. reflexivity. 
    }
  }
Qed.
     

