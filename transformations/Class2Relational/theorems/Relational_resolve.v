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
  Require ClassModelProperties RelationalModelProperties.

From transformations.Class2Relational Require Tactics.
From transformations.Class2Relational Require TraceUtils.


(** *** Utilities on transformation of elements *)

(* FIXME : not used here but could be useful elsewhere. *)
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

    (* Remark : exactly the same script as above. *)
Qed.


(* FIXME : not used here but could be useful elsewhere. *)
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
(*  Tactics.in_singleton_allTuples. FIXME : does not work*)
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

(* FIXME : not used here but could be useful elsewhere. *)
Lemma transform_class_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
      In (TableElement {| table_id := id; table_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (ClassElement {| class_id:= id ; class_name := name|}) (cm.(modelElements))
. 
Proof.
  (* Remark : (nearly) same script as above. *)
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
    destruct c.
    compute in H.
    remove_or_false H.
      injection H ; intros ;subst ; clear H.
      reflexivity.
  + auto.
Qed.





(** Concepts under focus in this module *)

Definition all_attributes_are_typed (cm : ClassModel) :=
  forall (att : Attribute_t),
      In (AttributeElement att) cm.(modelElements) ->
      exists (r:Class_t), 
        In (AttributeTypeLink {| source_attribute := att ; a_type := r |}) cm.(modelLinks) .

Definition all_columns_have_a_reference (rm : RelationalModel) :=
forall (col: Column_t),
      In (ColumnElement col) rm.(modelElements) ->
      exists r', In (ColumnReferenceLink {| cr := col ;  ct := r' |}) rm.(modelLinks).
  

Lemma wf_stable cm rm :
  rm = execute Class2Relational cm ->
  all_attributes_are_typed cm ->
  ClassModelProperties.wf_classmodel_types_exist cm ->
  ClassModelProperties.wf_classmodel_unique_attribute_types cm ->
  RelationalModelProperties.wf_all_table_references_exist rm.
Proof.
  intros T C_WF1 C_WF2 C_WF3.
  intros r t R_IN1.
  subst rm.
  
  Tactics.destruct_execute.
  rename IN_E into C_IN1.

  destruct t.
  apply transform_class_fw with (cm:=cm) ; [ reflexivity | ]. (* FIXME : don't want to destruct t to be able to apply transform_class_fw. *)

  repeat Tactics.destruct_any.
  
  clear IN0.
  
  (* we need to know which rule has been applied to preogress in the computation *)
  Tactics.destruct_In_two ; simpl in * ; 
  remove_or_false_auto ; subst ; simpl in * ;
  Tactics.deduce_element_kind_from_guard ; simpl in * ;
  [ | ].
  { (* first rule : impossible *)
    exfalso.

    (* Set Printing All.*)

    eapply Tactics.allModelElements_allTuples_back with (t:=Class2Relational) in C_IN1 ;
    (* FIXME : the tactics does not work*)
      simpl in *.
    repeat Tactics.destruct_any.
    unfold Parser.parseOutputPatternElement in IN2 ; simpl in *. 
    unfold applyElementOnPattern in IN2 ; simpl in IN2.
        
    rewrite app_nil_r in IN2.
    Tactics.destruct_in_optionListToList.
    
    unfold Parser.parseOutputPatternLink in M ; simpl in M.
    unfold ConcreteExpressions.makeLink in M ; simpl in M.
    unfold ConcreteExpressions.wrapLink in M ; simpl in M.
     
    Tactics.monadInv M.
    unfold maybeBuildTableColumns in M.
    
    Tactics.monadInv M.
    apply in_singleton in IN2 ; discriminate IN2.
  }
  {
    (* second rule *)

    (* Set Printing All.*)
    eapply Tactics.allModelElements_allTuples_back with (t:=Class2Relational) in C_IN1 ;
    (* FIXME : the tactics does not work*)
      simpl in *.
    repeat Tactics.destruct_any.
    unfold Parser.parseOutputPatternElement in IN2 ; simpl in *. 
    unfold applyElementOnPattern in IN2 ; simpl in IN2.
        
    rewrite app_nil_r in IN2.
    Tactics.destruct_in_optionListToList.
    
    unfold Parser.parseOutputPatternLink in M ; simpl in M.
    unfold ConcreteExpressions.makeLink in M ; simpl in M.
    unfold ConcreteExpressions.wrapLink in M ; simpl in M ;
      Tactics.monadInv M.

    apply in_singleton in IN2 ; Tactics.inj IN2.
    
    unfold maybeBuildColumnReference in M ; 
      Tactics.monadInv M.

    unfold ModelingSemantics.maybeResolve in M ;
      simpl in M.

    unfold ModelingSemantics.denoteOutput in M ; 
      Tactics.monadInv M.

    Ltac toEDataT H :=
      match type of H with
        toEData Table_K ?E = Some _ => destruct E ; [ | discriminate H] 
      end.

    toEDataT M.
    destruct t ; unfold toEData in M ; simpl in M ; Tactics.inj M.

    destruct a (* FIXME *). simpl in D ; subst derived.

    unfold maybeResolve in E ; 
      Tactics.monadInv E.
  
    unfold maybeSingleton in E0.
    unfold option_map in E0 ;
      Tactics.monadInv E0.

    unfold getAttributeTypeElement in E0.
    Tactics.monadInv E0.

    unfold singleton in E ; simpl in E.
    
    Tactics.duplicate C_IN1 C_IN2.
    apply C_WF1 in C_IN2 ; destruct C_IN2 as (t & C_IN2).
    rewrite ClassModelProperties.getAttributeType_In_left_3 with (t:=t) in E0 ;
      [ | exact C_WF3 | exact C_IN2]. 
    Tactics.inj E0.    
 
    unfold resolve in E.
    unfold resolveIter in E ;
      Tactics.monadInv E.


    destruct t ; simpl in * ; subst.  

    apply find_some in E ; simpl in *.
    destruct E as (T_IN1 & T_IN2).
    
    specialize (TraceUtils.trace_wf cm) ; intro T_WF.
    unfold TraceUtils.wf in T_WF.
    eapply List.Forall_forall in T_WF ; [ | exact T_IN1 ].
    inversion T_WF ; subst.
    destruct c ; subst ; simpl in *.
    
    eapply TraceUtils.in_trace_in_models in T_IN1 ; 
      destruct T_IN1 as (IN1 & IN2). 
    destruct c0 ; assumption.
  }
Qed.

(** *** Result *)



Theorem Relational_Column_Reference_definedness_aux:
forall (cm : ClassModel) (rm : RelationalModel), 

  (* well-formed *) ClassModelProperties.wf_classmodel_types_exist cm ->

  (* transformation *) rm = execute Class2Relational cm ->

  (* precondition *) all_attributes_are_typed cm  ->  

    (* postcondition *) all_columns_have_a_reference rm . 

Proof. 
  intros cm rm  WF2 E PRE.  intros col IN1. 
  subst rm.
  repeat Tactics.destruct_execute.
  repeat Tactics.show_singleton.
  repeat Tactics.show_origin.
  repeat Tactics.destruct_any.

  (* we have lost IN1 : In (ColumnElement col)
          (modelElements (execute Class2Relational cm)) *)

  clear IN_I. 
  
  apply Tactics.allModelElements_allTuples_back in IN_E.
  
  Tactics.duplicate PRE H.

  specialize (H _ IN_E).
  destruct H as (c & G1).
  Tactics.duplicate G1 IN_C ; apply WF2 in IN_C.  
  
  Tactics.duplicate G1 IN2. 
  unfold getColumnReference.

  unfold execute.  simpl. 

  set (z:=r).

  Tactics.destruct_In_two ; [ exfalso | ] ; 
   simpl in IN_OP ; remove_or_false IN_OP ; subst ope ; [ discriminate IN1 | Tactics.inj IN1]. 
  
  clear n. 
  simpl in M.
  
  Tactics.deduce_element_kind_from_guard. (* M *)
 
  destruct a0 ; simpl in *. (* derived a0 = false *)
  subst derived ; simpl in *. 

  Tactics.duplicate G1 G2. (* à quoi sert de garder PRE1 ? *)


  specialize (TraceUtils.in_maybeResolve_trace_2 c cm IN_C ) ; 
    intros (R & I).


  apply ClassModelProperties.getAttributeType_In_left_2 in G1 ;
    destruct G1 as [r G1].

  exists{| table_id := r.(class_id); table_name := r.(class_name) |}.

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
     
      

      rewrite G1.



      unfold ModelingSemantics.maybeResolve.

      apply ClassModelProperties.getAttributeType_classex_right in G1 ; [ | exact WF2].

      apply TraceUtils.in_maybeResolve_trace_2 in G1.
      destruct G1 as (G11 & G12).
      
      unfold maybeSingleton.
      unfold option_map.
      unfold singleton.
      rewrite G11.
      simpl.
      left.
      reflexivity.
    }
  }
Qed.


Theorem Relational_Column_Reference_definedness:
forall (cm : ClassModel) (rm : RelationalModel), 

(* well-formed *) ClassModelProperties.wf_classmodel_types_exist cm ->

  (* transformation *) rm = execute Class2Relational cm ->

  (* precondition *)  (forall (att : Attribute_t),
      In (AttributeElement att) cm.(modelElements) ->
      exists (r:Class_t), 
        getAttributeType att cm = Some r ) ->  

    (* postcondition *)  forall (col: Column_t),
      In (ColumnElement col) rm.(modelElements) ->
      exists r', getColumnReference col rm =Some r'. 

Proof. 
  intros cm rm WF E PRE.  intros col IN1.
  subst rm.

  repeat Tactics.destruct_execute.
  repeat Tactics.show_singleton.
  repeat Tactics.show_origin.
  repeat Tactics.destruct_any.

  (* we have lost IN1 : In (ColumnElement col)
          (modelElements (execute Class2Relational cm)) *)

  clear IN_I. 
  
  apply Tactics.allModelElements_allTuples_back in IN_E.
  
  Tactics.duplicate PRE H.

  specialize (H _ IN_E).
  destruct H as (c & G1). 
  Tactics.duplicate G1 IN_C.
  apply ClassModelProperties.getAttributeType_In_right in IN_C.
  eapply WF in IN_C.
  Tactics.duplicate G1 IN2. (* test *)
  apply ClassModelProperties.getAttributeType_In_right in IN2.
  unfold getColumnReference.

  unfold execute.  simpl. 

  set (z:=r).

  Tactics.destruct_In_two ; [ exfalso | ] ; 
   simpl in IN_OP ; remove_or_false IN_OP ; subst ope ; [ discriminate IN1 | Tactics.inj IN1]. 
  
  clear n. 
  simpl in M.
  
  Tactics.deduce_element_kind_from_guard. (* M *)
 
  destruct a0 ; simpl in *. (* derived a0 = false *)
  subst derived ; simpl in *. 

  Tactics.duplicate G1 G2. (* à quoi sert de garder PRE1 ? *)
  apply ClassModelProperties.getAttributeTypeOnLinks_In_right in G1.

  specialize (TraceUtils.in_maybeResolve_trace_2 c cm IN_C ) ; intros (R & I).


  eapply RelationalModelProperties.in_getColumnReferenceOnLinks_right 
    with (x:= {| table_id := c.(class_id) ;  
                table_name := c.(class_name) |}) . 

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
      rewrite G2. simpl.

      unfold ModelingSemantics.maybeResolve.
      unfold singleton.
      rewrite R. 

      simpl. left. reflexivity. 
    }
  }
Qed.
     



Theorem Relational_Column_Reference_definedness_altproof:
  forall (cm : ClassModel) (rm : RelationalModel), 
    
    (* well-formed *) ClassModelProperties.wf_classmodel_types_exist cm ->
    
    (* transformation *) rm = execute Class2Relational cm ->
    
    (* precondition *)  (forall (att : Attribute_t),
        In (AttributeElement att) cm.(modelElements) ->
        exists (r:Class_t), 
          getAttributeType att cm = Some r ) ->  
    
      (* postcondition *)  forall (col: Column_t),
        In (ColumnElement col) rm.(modelElements) ->
        exists r', getColumnReference col rm =Some r'. 

Proof. 
  intros cm rm WF E PRE.  intros col IN1.
  cut (all_columns_have_a_reference rm).
  {
    intro WT.
    unfold all_columns_have_a_reference in WT.
    apply WT in IN1.
    destruct IN1 as (r & IN2).
    apply RelationalModelProperties.in_getColumnReferenceOnLinks_right_2.
    eauto.
  }
  {
    apply Relational_Column_Reference_definedness_aux with (cm:=cm) ;
    [ exact WF | exact E | ].
    unfold all_attributes_are_typed.
    intros att IN2.
    apply PRE in IN2.
    destruct IN2 as (r & G).
    apply ClassModelProperties.getAttributeType_In_right in G.
    eauto.
  }
Qed.


Corollary Relational_Column_Reference_definedness_2:
  forall (cm : ClassModel) (rm : RelationalModel), 
    
    (* well-formed (1/2) *) 
    ClassModelProperties.wf_classmodel_types_exist cm ->
    
    (* well-formed (2/2) *) 
    ClassModelProperties.wf_classmodel_unique_attribute_types cm ->
    
    (* transformation *) 
    rm = execute Class2Relational cm ->
    
    (* precondition *)  
    (forall (att : Attribute_t),
        In (AttributeElement att) cm.(modelElements) ->
        exists (r:Class_t), 
          getAttributeType att cm = Some r ) ->  
    
    (* postcondition *)  
    forall (col: Column_t),
        In (ColumnElement col) rm.(modelElements) ->
        exists r', (getColumnReference col rm = Some r' 
                    /\ In (TableElement r') rm.(modelElements)). 

Proof. 
  intros cm rm WF1 WF2 T WF3 col IN .
  cut (exists r' : Table_t,
          getColumnReference col rm = return r').
  {
    intros (r & G).
    exists r.
    split ; [ exact G | ].
    eapply wf_stable ; [ exact T |  | exact WF1  | exact WF2 | ].
    {
      (* comes from WF3 *)
      unfold all_attributes_are_typed.  
      intros att IN2.
      apply WF3 in IN2.
      destruct IN2 as (r2 & G2).
      apply ClassModelProperties.getAttributeType_In_right in G2.
      eauto.
    }
    {
      (* comes from G *)
      apply RelationalModelProperties.in_getColumnReferenceOnLinks_left.
      exact G.
    }
  }
  {
    eapply Relational_Column_Reference_definedness ; eassumption.
  }
Qed.
