Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.

From core 
  Require Import 
  utils.Utils Semantics modeling.ModelingMetamodel Model.

From transformations.Class2Relational
  Require Import Class2Relational ClassMetamodel RelationalMetamodel.

From usertools 
  Require ResolveTools.

From transformations.Class2Relational 
  Require 
    ClassModelProperties RelationalModelProperties 
    C2RTactics TraceUtils Elements.

Import Glue.

(** ** Concepts under focus in this module. *)

(** *** On class models *)

Definition all_attributes_are_typed (cm : ClassModel) :=
  forall (att : Attribute_t),
      In (AttributeElement att) cm.(modelElements) ->
      exists (r:Class_t), 
        In (Attribute_typeLink {| src := att ; trg := r |}) cm.(modelLinks) .


(** *** On relational models *)

Definition all_columns_have_a_reference (rm : RelationalModel) :=
forall (col: Column_t),
      In (ColumnElement col) rm.(modelElements) ->
      exists r', In (Column_referenceLink {| src := col ;  trg := r' |}) rm.(modelLinks).
 
  

(** ** Some tactics related to Class2Relational *)

Ltac tmp H := 
  repeat monadInv H ;
  unfold ModelingSemantics.resolve in H  ;
  ModelingSemantics.inv_denoteOutput H ; 
  C2RTactics.toEDataT H ;
  C2RTactics.unfold_toEData H ;
  PropUtils.inj H .


(** ** Important lemma *)
Lemma wf_stable cm rm :
  rm = execute Class2Relational cm ->
  all_attributes_are_typed cm ->
  ClassModelProperties.wf_classmodel_types_exist cm ->
  ClassModelProperties.wf_classmodel_unique_attribute_types cm ->
  RelationalModelProperties.wf_all_table_references_exist rm.
Proof.
  intros T C_WF1 C_WF2 C_WF3.
  intros c tb R_IN1.
  subst rm.

  TacticsBW.exploit_link_in_result R_IN1 ; [].

  (* EQ and EQ0 are not needed here *)
  clear EQ EQ0.

  (* Exploit MATCH_GUARD *)
  C2RTactics.negb_inv MATCH_GUARD.
  destruct t ; simpl in MATCH_GUARD ; subst Attribute_derived.

  (* Exploit Resolve / IN_L *)
  (* IN_L contains the code of the link-pattern in the rule. *)
  tmp IN_L. (* fixme *)
  

  (* Exploit Resolve. *)
  rename EQ into R.
  apply ResolveTools.tr_resolve_leaf in R.
  
  apply TraceLink.in_drop_inv in R ;
  destruct R as (? & R) ; simpl in R.
  apply <- SemanticsTools.in_modelElements_inv.
  eauto.
Qed.


(** ** Main Result *)


Theorem Relational_Column_Reference_definedness_1:
forall (cm : ClassModel) (rm : RelationalModel), 

  (* well-formed *) ClassModelProperties.wf_classmodel_types_exist cm ->

  (* transformation *) rm = execute Class2Relational cm ->

  (* precondition *) all_attributes_are_typed cm  ->  

    (* postcondition *) all_columns_have_a_reference rm . 

Proof. 
  intros cm rm  WF2 E PRE.  intros col IN_COL. 
  subst rm.


  TacticsBW.exploit_element_in_result IN_COL (* or apply Elements.transform_attribute_bw (moins puissant car on perd l'info sur la garde) *) ; [].
  compute in t0.

  C2RTactics.negb_inv MATCH_GUARD.
  
  specialize (PRE _ IN_ELTS0).
  destruct PRE as (c & G1).

  
  destruct t0.  
  unfold C2RTactics.convert_attribute.
  simpl (ClassMetamodel.Attribute_id _)  in *.
  simpl (ClassMetamodel.Attribute_name _) in *. 
   simpl ClassMetamodel.Attribute_derived in *. (* derived a = false *)
  subst Attribute_derived. 

 
  apply ClassModelProperties.getAttributeType_In_left in G1 ; (* here we should exploit ClassModelProperties.getAttributeType_In_left_wf *)
    destruct G1 as [r G1].

  exists{| Table_id := r.(Class_id); Table_name := r.(Class_name) |}.

(* Alternative *)
  TacticsFW.transform_link_fw_tac_singleton 2 1 0 ; []. 
(*  TacticsFW.transform_link_fw_tac_singleton_auto 0 ; []. *)

    simpl. 
    unfold Parser.dropToList ; simpl.
    unfold getAttribute_typeElement.
    simpl.
    unfold ConcreteExpressions.makeLink ; simpl.
    unfold ConcreteExpressions.wrapLink ; simpl.
    rewrite G1.
    simpl.
    unfold singleton ; simpl.

    apply ClassModelProperties.getAttributeType_classex_right in G1 ; [ | exact WF2].

    apply TraceUtils.in_model_resolve in G1. 
    destruct G1 as (G11 & G12).
    unfold ModelingSemantics.resolve.
    rewrite G11.
    TacticUtils.first_in_list.
Qed.

     

(** With an additional hypothesis on well-formedness of the source model, we get a better result on the produced model. *)

Corollary Relational_Column_Reference_definedness_not_used :
  forall (cm : ClassModel) (rm : RelationalModel), 
    
    (* well-formed (1/2) *) 
    ClassModelProperties.wf_classmodel_types_exist cm ->
    
    (* well-formed (2/2) *) 
    ClassModelProperties.wf_classmodel_unique_attribute_types cm ->
    
    (* transformation *) 
    rm = execute Class2Relational cm ->
    
    (* precondition *)  
    all_attributes_are_typed cm ->
    
    (* postcondition *)  
    forall (col: Column_t),
        In (ColumnElement col) rm.(modelElements) ->
        exists r', (In (Column_referenceLink {| src := col ;  trg := r' |}) rm.(modelLinks) 
                    /\ In (TableElement r') rm.(modelElements)). 

Proof. 
  intros cm rm WF1 WF2 T WF3 col IN .
  cut (exists r' : Table_t,
          In (Column_referenceLink {| src := col ;  trg := r' |}) rm.(modelLinks)
       ).
  {
    intros (r & G).
    exists r.
    split ; [ exact G | ].
    eapply wf_stable ; [ exact T | exact WF3 | exact WF1  | exact WF2 | exact G ].
  }
  { eapply Relational_Column_Reference_definedness_1 ; eassumption. }
Qed.


(** * Same results with [get] instead of [In] *) 
(** ** Concepts under focus in this module. *)

(** *** On class models *)


Definition all_attributes_are_typed_2 (cm : ClassModel) :=
  forall (att : Attribute_t),
    In (AttributeElement att) cm.(modelElements) ->
    exists (r:Class_t), 
      getAttribute_type att cm = Some r.

(** *** On relational models *)

 
Definition all_columns_have_a_reference_2 (rm : RelationalModel) :=
forall (col: Column_t),
      In (ColumnElement col) rm.(modelElements) ->
      exists r',  getColumn_reference col rm =Some r'.

(** ** Results *)

(** We use the result above to prove a similar result with [get] instead of [In]. *)
Corollary Relational_Column_Reference_definedness_2 :
  forall (cm : ClassModel) (rm : RelationalModel), 
    
    (* well-formed *) ClassModelProperties.wf_classmodel_types_exist cm ->
    
    (* transformation *) rm = execute Class2Relational cm ->
    
    (* precondition *)  all_attributes_are_typed_2 cm  ->  
    
      (* postcondition *)  all_columns_have_a_reference_2 rm . 

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
    apply Relational_Column_Reference_definedness_1 with (cm:=cm) ;
    [ exact WF | exact E | ].
    unfold all_attributes_are_typed.
    intros att IN2.
    apply PRE in IN2.
    destruct IN2 as (r & G).
    apply ClassModelProperties.getAttributeType_In_right in G.
    eauto.
  }
Qed.



(** With an additional hypothesis on well-formedness of the source model, we get again a better result on the produced model. *)
Corollary Relational_Column_Reference_definedness_3 :
  forall (cm : ClassModel) (rm : RelationalModel), 
    
    (* well-formed (1/2) *) 
    ClassModelProperties.wf_classmodel_types_exist cm ->
    
    (* well-formed (2/2) *) 
    ClassModelProperties.wf_classmodel_unique_attribute_types cm ->
    
    (* transformation *) 
    rm = execute Class2Relational cm ->
    
    (* precondition *)  
    all_attributes_are_typed_2 cm ->
    
    (* postcondition *)  
    forall (col: Column_t),
        In (ColumnElement col) rm.(modelElements) ->
        exists r', (getColumn_reference col rm = Some r' 
                    /\ In (TableElement r') rm.(modelElements)). 

Proof. 
  intros cm rm WF1 WF2 T WF3 col IN .
(* FIXME : can we use [Relational_Column_Reference_definedness_not_used] here ? *)
  cut (exists r' : Table_t,
          getColumn_reference col rm = return r').
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
  { eapply Relational_Column_Reference_definedness_2 ; eassumption. }
Qed.
