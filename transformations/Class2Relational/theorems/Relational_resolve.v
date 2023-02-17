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
  

(** Some tactics *)


(* same as Tactics.destruct_in_optionListToList but switches the names of the produced hypothsesis *)

Lemma optionListToList_Some {A} :
  forall (a: list A), optionListToList (Some a) = a.
Proof.
  reflexivity.
Qed.

Ltac unfold_evalOutputPatternElementExpr H :=
  unfold Expressions.evalOutputPatternElementExpr in H ;
  unfold Syntax.ope_elementExpr in H.

Ltac unfold_evalOutputPatternLinkExpr H :=
  unfold Expressions.evalOutputPatternLinkExpr in H ;
  unfold Syntax.ope_linkExpr in H.

Ltac unfold_maybeResolveAll H :=
  unfold ModelingSemantics.maybeResolveAll in H ;
  unfold Semantics.maybeResolveAll in H.

Ltac progress_in_applyElementOnPattern H :=
    unfold applyElementOnPattern in H ;
    unfold_evalOutputPatternElementExpr H ;

    C2RTactics.unfold_make_element H ;
    ListUtils.destruct_in_optionListToList H ;
    
    unfold_evalOutputPatternLinkExpr H ;
    try rewrite flat_map_singleton in H ; 
    
    C2RTactics.unfold_make_link H  ; 
    
    simpl constructor in H ;
    
    cbv match in H ;
    Tactics.simpl_accessors_any H  ;
    PropUtils.inj H.

Ltac suite H :=
  ListUtils.destruct_in_optionListToList H ;
  OptionUtils.monadInv H.


Ltac toEDataT H :=
   match type of H with
     toEData Table_K ?E = Some _ => destruct E ; [ | discriminate H] 
   end.

 
 Ltac progress_in_maybeBuildColumnReference H := 
  match type of H with 
  | maybeBuildColumnReference _ _ = Some _ =>
     inv_maybeBuildColumnReference H ; 
     unfold ModelingSemantics.maybeResolve in H  ;
     ModelingSemantics.inv_denoteOutput H ; 
     toEDataT H ;
     C2RTactics.unfold_toEData H ;
     PropUtils.inj H
  end.

 

(** important lemma *)

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
  
  (* (1) *)
  destruct (Tactics.destruct_in_modelLinks_execute_lem R_IN1) 
    as ( elts & r & i & ope & IN_E & IN_RULE & MATCH_RULE & IN_IT & IN_OUTPAT & IN_APP_PAT).

  (* (2) Select a rule. *)
  Tactics.progress_in_In_rules IN_RULE ; [ | ] ; 

  (* (3) *)
  Tactics.progress_in_ope IN_OUTPAT ; 

  (* (4) Now we can progress in the guard. *)
  Tactics.exploit_evalGuard MATCH_RULE ;

  
  (* (5.L) now we can progress in IN_APP_PAT. *)
  unfold Parser.parseOutputPatternElement in IN_APP_PAT ;
  Semantics.exploit_In_applyElementOnPattern IN_APP_PAT EV_OUTPAT ;

  
  ListUtils.destruct_in_optionListToList IN_APP_PAT ;
  unfold Expressions.evalOutputPatternLinkExpr in IN_APP_PAT ;
  unfold Syntax.ope_linkExpr in IN_APP_PAT ;
  unfold ConcreteSyntax.r_InKinds in IN_APP_PAT ;
  unfold ConcreteSyntax.e_OutKind in IN_APP_PAT ;
  unfold ConcreteSyntax.e_outlink in IN_APP_PAT ;
  unfold Parser.parseOutputPatternLinks in IN_APP_PAT ;
  unfold ConcreteExpressions.makeElement in IN_APP_PAT ; 


  unfold Expressions.evalOutputPatternElementExpr in EV_OUTPAT ; 
  unfold Syntax.ope_elementExpr in EV_OUTPAT ; 
  unfold ConcreteSyntax.r_InKinds in EV_OUTPAT ; 
  unfold ConcreteSyntax.e_OutKind in EV_OUTPAT ; 
  unfold ConcreteSyntax.e_outpat in EV_OUTPAT ; 

  unfold ConcreteExpressions.makeElement in EV_OUTPAT ;
  unfold ConcreteExpressions.wrapElement  in EV_OUTPAT ;
  monadInv EV_OUTPAT ; [ | ] ;
  repeat ConcreteExpressions.wrap_inv EV_OUTPAT ;

  PropUtils.inj IN_APP_PAT ;

  rewrite List.app_nil_r in IN ;

  ListUtils.destruct_in_optionListToList IN ;

  unfold Parser.parseOutputPatternLink in IN ;
  unfold ConcreteSyntax.o_OutRefKind in IN ;
  unfold ConcreteSyntax.o_outpat in IN ;
  unfold ConcreteExpressions.makeLink in IN ;
  unfold ConcreteExpressions.wrapLink in IN ;
  monadInv IN ; [ | ] ;
  monadInv IN ; [ | ] ;
  repeat ConcreteExpressions.wrap_inv E ; [ | ] ;
  monadInv IN ; [ | ] ;
  compute in E0 (*toEData *) ; PropUtils.inj E0 ;

  repeat ListUtils.unfold_In_cons IN0 (* fixme : IN0 not introduced (from suite)*) ; 
    first [ discriminate IN0 (* discard rules that do not match *)
          | PropUtils.inj IN0 ] ; [].



  (* (6) *)
  Tactics.exploit_in_it IN_IT. 

  (* (7) *)
  Semantics.exploit_in_allTuples IN_E.

  C2RTactics.negb_inv MATCH_RULE.
  destruct t ; simpl in MATCH_RULE ; subst derived.
  
  progress_in_maybeBuildColumnReference IN.
  
  core.Semantics.progress_maybeResolve E. 
  
  ListUtils.inv_maybeSingleton E0.
  
  inv_getAttributeTypeElement E0.
  
  eapply TraceUtils.in_trace_in_models_target ; eauto. 
  
Qed.


(** *** Main Results *)


Theorem Relational_Column_Reference_definedness_aux:
forall (cm : ClassModel) (rm : RelationalModel), 

  (* well-formed *) ClassModelProperties.wf_classmodel_types_exist cm ->

  (* transformation *) rm = execute Class2Relational cm ->

  (* precondition *) all_attributes_are_typed cm  ->  

    (* postcondition *) all_columns_have_a_reference rm . 

Proof. 
  intros cm rm  WF2 E PRE.  intros col IN1. 
  subst rm.

  (* 1 *)
  destruct (Tactics.destruct_in_modelElements_execute_lem IN1) 
    as (r & sp & n & ope & IN_E & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & IN1'). 

  (* (2) *)
  Tactics.progress_in_In_rules IN_RULE ; [ | ] ;

  (* (3) *)   
  Tactics.progress_in_ope IN_OP ;

  (* (4) *)   
  Tactics.exploit_evalGuard MATCH_GUARD ;
  
  (* (5.E) *) 
  Tactics.exploit_evaloutpat IN1' ; [].
  
  (* (6) *)
  Tactics.exploit_in_it IN_IT.

  (* (7) *)
  Semantics.exploit_in_allTuples IN_E.
  
  Tactics.duplicate PRE H.

  specialize (H _ IN_E).
  destruct H as (c & G1).
  Tactics.duplicate G1 IN_C ; apply WF2 in IN_C.  
  
  Tactics.duplicate G1 IN2. 

  unfold execute ;  simpl. 

  C2RTactics.negb_inv MATCH_GUARD.

  destruct t0 ; simpl in *. (* derived a = false *)
  subst derived ; simpl in *. 

  Tactics.duplicate G1 G2. 

  specialize (TraceUtils.in_maybeResolve_trace_2 c cm IN_C ) ; 
    intros (R & I).

  apply ClassModelProperties.getAttributeType_In_left in G1 ; (* here we should exploit ClassModelProperties.getAttributeType_In_left_wf *)
    destruct G1 as [r G1].

  exists{| table_id := r.(class_id); table_name := r.(class_name) |}.

  apply in_flat_map.
  exists ([AttributeElement {|
               attr_id := attr_id;
               derived := false;
               attr_name := attr_name
             |}]).
  split.
  { apply C2RTactics.allModelElements_allTuples. exact IN_E. }
  {
    unfold applyPattern.
    apply in_flat_map.
    exists (Parser.parseRule R2).
    
    split.
    { simpl. auto. }
    { 
      apply tr_applyRuleOnPattern_in ; simpl.
      exists 0.
      split ; [ solve [auto] | ].
      apply tr_applyIterationOnPattern_in.
      eexists  ; split ; [ solve [simpl ; auto] | ].
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

  (* (1) *)
  destruct (Tactics.destruct_in_modelElements_execute_lem IN1) 
    as (r & sp & n & ope & IN_E & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & IN1'). 

  (* (2) *)
  Tactics.progress_in_In_rules IN_RULE ;
  
  (* (3) *)
  Tactics.progress_in_ope IN_OP ;  

  (* (4) *) 
  Tactics.exploit_evalGuard MATCH_GUARD ;
  
  (* (5.E) *)
  Tactics.exploit_evaloutpat IN1' ; [] ;

  (* (6) *)
  Tactics.exploit_in_it IN_IT ;  
  
  (* (7) *)
  Semantics.exploit_in_allTuples IN_E.
  
  Tactics.duplicate PRE H.

  specialize (H _ IN_E).
  destruct H as (c & G1). 
  Tactics.duplicate G1 IN_C.
  apply ClassModelProperties.getAttributeType_In_right in IN_C.
  eapply WF in IN_C.
  Tactics.duplicate G1 IN2. (* test *)
  apply ClassModelProperties.getAttributeType_In_right in IN2.
  unfold getColumnReference.

  unfold execute ; simpl. 

  C2RTactics.negb_inv MATCH_GUARD.
  destruct t0 ; simpl in *. (* derived a0 = false *)
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
  { apply C2RTactics.allModelElements_allTuples. exact IN_E. }
  {
    
    unfold applyPattern.
    apply in_flat_map.
    exists (Parser.parseRule R2).
  
    split.
    { simpl. auto. }
    { 
      apply tr_applyRuleOnPattern_in ; simpl.
      exists 0.
      split ; [ solve [auto] | ].
      apply tr_applyIterationOnPattern_in.
      eexists  ; split ; [ solve [ simpl ; auto] | ].
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
  { eapply Relational_Column_Reference_definedness ; eassumption. }
Qed.
