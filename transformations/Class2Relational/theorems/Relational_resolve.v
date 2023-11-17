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

From transformations.Class2Relational 
  Require C2RTactics TraceUtils Elements.

Import Glue.

(** ** Concepts under focus in this module. *)

(** *** On class models *)

Definition all_attributes_are_typed (cm : ClassModel) :=
  forall (att : Attribute_t),
      In (AttributeElement att) cm.(modelElements) ->
      exists (r:Class_t), 
        In (Attribute_typeLink {| left_glue := att ; right_glue := r |}) cm.(modelLinks) .


(** *** On relational models *)

Definition all_columns_have_a_reference (rm : RelationalModel) :=
forall (col: Column_t),
      In (ColumnElement col) rm.(modelElements) ->
      exists r', In (Column_referenceLink {| left_glue := col ;  right_glue := r' |}) rm.(modelLinks).
 
  

(** ** Some tactics related to Class2Relational *)

Ltac toEDataT H :=
   match type of H with
     toEData Table_K ?E = Some _ => destruct E ; [ | discriminate H] 
   end.

 
Ltac tmp H := 
  repeat monadInv H ;
  unfold ModelingSemantics.resolve in H  ;
  ModelingSemantics.inv_denoteOutput H ; 
  toEDataT H ;
  C2RTactics.unfold_toEData H ;
  PropUtils.inj H .

Ltac progress_in_maybeBuildColumnReference H := 
  match type of H with 
  | option_map (Build_Glue _) _ = Some _  =>
     inv_maybeBuildColumnReference H ; 
     unfold ModelingSemantics.maybeResolve in H  ;
     ModelingSemantics.inv_denoteOutput H ; 
     toEDataT H ;
     C2RTactics.unfold_toEData H ;
     PropUtils.inj H
  end.

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

  Tactics.exploit_link_in_result R_IN1 ; [ | ] ;  
    
  clear R_IN1 ;
  
  first [discriminate IN | inj IN ] ; []. 
  
  simpl in IN_L.


  C2RTactics.negb_inv MATCH_GUARD.
  destruct t ; simpl in MATCH_GUARD ; subst Attribute_derived.

  tmp IN_L.
  (*progress_in_maybeBuildColumnReference IN_L.*)
  
  unfold get_E_data in EQ ; inj EQ.
  core.Resolve.inv_resolve EQ1. 
  apply List.find_some in EQ1 ; destruct EQ1.
  (*ListUtils.inv_maybeSingleton EQ.*)
  
  inv_getAttribute_typeElement EQ0.

  destruct t ; simpl in H ; subst.   

  eapply Tactics.in_trace_in_models_target ; eauto. 

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


  Tactics.exploit_element_in_result IN_COL (* or apply Elements.transform_attribute_bw (moins puissant car on perd l'info sur la garde) *) ; []; 
  clear IN_COL.
  
  specialize (PRE _ IN_ELTS).
  destruct PRE as (c & G1).

  C2RTactics.negb_inv MATCH_GUARD.
  
  destruct t0. simpl (ClassMetamodel.Attribute_id _)  in * ; simpl (ClassMetamodel.Attribute_name _) in * ; simpl ClassMetamodel.Attribute_derived in *. (* derived a = false *)
  subst Attribute_derived. 

 
  apply ClassModelProperties.getAttributeType_In_left in G1 ; (* here we should exploit ClassModelProperties.getAttributeType_In_left_wf *)
    destruct G1 as [r G1].

  exists{| Table_id := r.(Class_id); Table_name := r.(Class_name) |}.

  eapply Tactics.in_links_fw with (tc:=C2RConfiguration) ; simpl.
  
  { apply incl_singleton. eassumption. }
  { auto. }
  { (* no auto *) simpl. right. left. reflexivity. (* rule R2 *) }
  { auto. }
  { simpl. instantiate (1:=0). auto. }
  { simpl ; auto. }
  { crush. }
  { crush. 
    unfold Parser.dropToList ; simpl.
    unfold getAttribute_typeElement.
    unfold Parser.parseOutputPatternLink.
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
    simpl.
    auto.
  }
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
        exists r', (In (Column_referenceLink {| left_glue := col ;  right_glue := r' |}) rm.(modelLinks) 
                    /\ In (TableElement r') rm.(modelElements)). 

Proof. 
  intros cm rm WF1 WF2 T WF3 col IN .
  cut (exists r' : Table_t,
          In (Column_referenceLink {| left_glue := col ;  right_glue := r' |}) rm.(modelLinks)
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
