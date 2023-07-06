Require Import core.Semantics.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Require Certification.

Import Metamodel.

(** * General purpose tactics *)

Ltac destruct_match :=
  match goal with 
     [ |- context[match ?P with | _ => _ end]] => destruct P 
  end. 

Ltac destruct_if_hyp :=
  let E := fresh "E" in
 match goal with
        [ H : context[if ?B then _ else _] |- _ ] => destruct B eqn:E 
 end.

Ltac destruct_if_goal :=
  let E := fresh "E" in
 match goal with
        [ |- context[if ?B then _ else _] ] => destruct B eqn:E 
 end.

(* To replace the [inversion] tactics on equalities on a dependant type constructor. *)
Ltac dep_inversion H := 
  let H':= fresh H in
  inversion H as [H'] ; apply Eqdep.EqdepTheory.inj_pair2 in H'.

  
Ltac duplicate H1 H2 := remember H1 as H2 eqn:TMP ; clear TMP.






(** * Tactics to transform an hypothesis H : In [e] (allTuples _ cm)
    into H: In (e) (modelElements cm)
*)

Import Model.

Lemma allModelElements_allTuples {tc:TransformationConfiguration} e t cm: 
  In e cm.(modelElements) ->
  0 < Syntax.arity t ->
  In [e] (allTuples t cm).
Proof. 
  intros.
  apply Certification.allTuples_incl_length.
   + apply incl_singleton. assumption.
   + compute. auto.
Qed.






(** * Destructors *)

Ltac destruct_in_modelElements_execute H :=
  match type of H with 
    In _ ( (execute ?T _).(modelElements))  =>
      let H2 := fresh "IN_E" in
      let e := fresh "sp" in
      rewrite (core.Certification.tr_execute_in_elements T) in H ;
      destruct H as [e [H2 H]]
  end.

Ltac destruct_in_modelLinks_execute H NEWNAME := 
  match type of H with
    In _ (modelLinks (execute ?T _)) =>
      let e := fresh "sp" in
      rewrite (core.Certification.tr_execute_in_links T) in H;
      destruct H as [e [NEWNAME H]]                                           
  end.     


Ltac destruct_instantiateOnPiece H IN_MATCH_NEWNAME :=
  match type of H with 
    In _ (elements_proj (traceTrOnPiece ?T _ _)) =>
      let e := fresh "r" in
      rewrite (core.Certification.tr_instantiateOnPiece_in T) in H ;
      destruct H as [e [IN_MATCH_NEWNAME H]]
  end.



Ltac destruct_in_matchingRules H NEWNAME :=
  match type of H with 
    | In _ (matchingRules ?T _ _)  =>
      rewrite (core.Certification.tr_matchingRules_in T) in H ;
      destruct H as [H NEWNAME]
  end.

Ltac destruct_in_matchingRules_auto :=
  match goal with 
    [ H : In _ (matchingRules _ _ _) |- _ ] =>
      let H2 := fresh "M" in
      destruct_in_matchingRules H H2
  end.



Ltac destruct_instantiateRuleOnPiece H IN_IT_NEWNAME:=
  match type of H with 
    In _ (elements_proj (traceRuleOnPiece _ _ _)) =>
      let e := fresh "n" in
      rewrite (core.Certification.tr_instantiateRuleOnPiece_in) in H ;
      destruct H as [e [IN_IT_NEWNAME H]]
  end.


Ltac destruct_instantiateIterationOnPiece H NEWNAME :=
  match type of H with 
    In _ (elements_proj (traceIterationOnPiece _ _ _ _)) =>
      let e := fresh "opu" in
      apply core.Certification.tr_instantiateIterationOnPiece_in in H ;
      destruct H as [e [NEWNAME H]]
  end.


Ltac destruct_apply_pattern H IN_MATCH_NEWNAME :=
  match type of H with 
    In _ (applyTrOnPiece _ _ _) => 
      let R := fresh "r" in
      apply core.Certification.tr_applyOnPiece_in in H ; 
      destruct H as (R & (IN_MATCH_NEWNAME & H))
end.

Ltac destruct_apply_pattern_auto :=
  match goal with 
    [ H : In _ (applyTrOnPiece _ _ _) |- _ ] => 
      let IN1 := fresh "IN_MATCH" in
      destruct_apply_pattern H IN1
end.

Ltac destruct_applyRuleOnPiece H NEW1 NEW2 :=
  match type of H with
    | In _ (applyRuleOnPiece _ _ _ _) =>
      let N := fresh "n" in 

      apply core.Certification.tr_applyRuleOnPiece_in in H ;
      destruct H as (N & (NEW1 & NEW2))
  end.

Ltac destruct_applyRuleOnPiece_auto :=
  match goal with
    [ H : In _ (applyRuleOnPiece _ _ _ _) |- _ ] =>
      let IN1 := fresh "IN_IT" in 
      let IN2 := fresh "IN_APP_PAT" in 
      destruct_applyRuleOnPiece H IN1 IN2
  end.

Ltac destruct_applyIterationOnPiece H NEWNAME :=
  match type of H with
    | In _ (applyIterationOnPiece _ _ _ _ _ )  =>
      let p := fresh "p" in
      apply core.Certification.tr_applyIterationOnPiece_in in H ;
      destruct H as (p & (NEWNAME & H))
  end.

Ltac destruct_applyIterationOnPiece_auto :=
  match goal with
    [ H : In _ (applyIterationOnPiece _ _ _ _ _ ) |- _ ] =>
      destruct_applyIterationOnPiece H
  end.

(** On traces. *)
Ltac destruct_trace H :=
  match type of H with 
  | In _ (traceTrOnModel _ _ )  => 
      let p:= fresh "p" in
      let IN := fresh "IN" in
      unfold traceTrOnModel in H ;
      apply in_flat_map in H ; 
      destruct H as (p & (IN & H))
  | _ => fail "Failure in destruct_trace."
  end.

Ltac destruct_traceOnPiece H :=
  match type of H with 
    | In _ (traceTrOnPiece _ _ _) => 
        let p:= fresh "r" in
        let IN := fresh "IN" in
        unfold traceTrOnPiece in H ;
        apply in_flat_map in H ; 
        destruct H as (p & (IN & H))
  | _ => fail "Failure in destruct_traceOnPiece."
  end.


Ltac destruct_traceRuleOnPiece H :=
  let p:= fresh "i" in
  let IN := fresh "IN" in
  match type of H  with 
    | In _ (traceRuleOnPiece _ _ _) => 
      unfold traceRuleOnPiece in H ;
      apply in_flat_map in H ; 
      destruct H as (p & (IN & H))
  | _ => fail "Failure in destruct_traceRuleOnPiece."
  end.

Ltac destruct_traceIterationOnPiece H :=
  match type of H with 
    | In _ (traceIterationOnPiece _ _ _ _) => 
        let p:= fresh "e" in
        let IN := fresh "IN" in
        unfold traceIterationOnPiece in H ;
        apply in_flat_map in H ; 
        destruct H as (p & (IN & H))
  | _ => fail "Failure in destruct_traceIterationOnPiece."
  end.



Ltac destruct_in_optionToList H :=
  let TMP := fresh "TMP" in
  match type of H with 
    | In _ (optionToList _) => apply in_optionToList in H
  end.

Ltac destruct_in_optionToList_auto :=
  let TMP := fresh "TMP" in
  match goal with 
    [ H : In _ (optionToList _) |- _ ] => destruct_in_optionToList H
  end.



Lemma destruct_in_trace_lem {MM1 : Metamodel} {T1} {T2} {BEQ} :
  forall
    {t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ))} 
  {cm} {l},
  In l (RichTraceLink.drop ((traceTrOnModel) t cm)) ->
  exists p r i outpat te,   
    In p (allTuples t cm)
    /\ In r (Syntax.rules t) 
    /\ UserExpressions.evalGuard r cm p = true 
    /\ In i (seq 0 (UserExpressions.evalIterator r cm p))
    /\ In outpat (Syntax.r_outputPattern r)
    /\ l = {|
             PoorTraceLink.source := (p, i, Syntax.opu_name outpat);
             PoorTraceLink.produced := te
           |} 
    /\ UserExpressions.evalOutputPatternUnit outpat cm p i = return te .
Proof.
  intros.
  unfold RichTraceLink.drop in H.
  apply in_map_iff in H.
  destruct H as (lk0, (CONV, H)).
  destruct_trace H ; 
  destruct_traceOnPiece H ; 
  destruct_traceRuleOnPiece H ; 
  destruct_traceIterationOnPiece H ; 
  destruct_in_optionToList H.
  Tactics.destruct_in_matchingRules IN0 M.
  unfold traceElementOnPiece in H.
 
  OptionUtils.monadInv H.
  unfold RichTraceLink.convert ; simpl.
  eauto 12.
Qed.

Corollary in_trace_in_models_source {MM1} {T1} {T2} {BEQ} :  
  forall (t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ)))
 cm a b s i,
    In (PoorTraceLink.buildTraceLink ([a],i,s) b ) (RichTraceLink.drop (traceTrOnModel t cm)) ->
    In a cm.(modelElements) .
Proof.
  intros t cm a b s i IN.

  destruct (destruct_in_trace_lem IN) 
    as (se & r & n & e & te & IN_SOURCE & _ & _ & _ & _ & EQ & _).

  inj EQ.

  Semantics.in_allTuples_auto.

  exact IN_SOURCE.
Qed.

Lemma in_trace_in_models_target {MM1:Metamodel} {T1} {T2} {BEQ} :
  forall 
    (t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ)))
    cm a b,
     In (PoorTraceLink.buildTraceLink a b) (RichTraceLink.drop (traceTrOnModel t cm)) ->
    In b (execute t cm).(modelElements).
Proof.
  intros t cm a b IN.
  unfold execute. 
  unfold modelElements. 
  unfold RichTraceLink.drop in IN.
  apply in_map_iff. 
  apply in_map_iff in IN. 
  destruct IN as (x & C & IN). 
  exists x. 
  split ; [ | assumption ]. 
  destruct x ; unfold RichTraceLink.convert in C. 
  congruence.
Qed.


Lemma destruct_in_modelElements_execute_lem {MM1} {T1} {T2} {BEQ} :
  forall 
    {t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ))} 
    {cm} {a},
    
  In a
    (modelElements (execute t cm)) ->
  exists r sp n0 opu,
    In sp (allTuples t cm)
    /\ In r (Syntax.rules t) 
    /\ UserExpressions.evalGuard r cm sp = true 
    /\ In n0 (seq 0 (UserExpressions.evalIterator r cm sp))
    /\ In opu (Syntax.r_outputPattern r) 
    /\ UserExpressions.evalOutputPatternUnit opu cm sp n0 = Some a.
Proof.
  intros. 
  destruct_in_modelElements_execute H.  
  destruct_instantiateOnPiece H NEW1. 
  destruct_instantiateRuleOnPiece H NEW2. 
  destruct_instantiateIterationOnPiece H NEW3. 
  unfold traceElementOnPiece in H.
  OptionUtils.monadInv H.
  OptionUtils.monadInv H.
  simpl RichTraceLink.produced.
  destruct_in_matchingRules NEW1 NEW4. 
  eauto 10.
Qed.


(** For the user *) 
Lemma in_modelElements_execute_left {MM1} {T1} {T2} {BEQ} :
  forall 
    {t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ))} 
    {cm} {a},
    
  forall r sp n0 opu,
    In sp (allTuples t cm) ->
    In r (Syntax.rules t) ->
    UserExpressions.evalGuard r cm sp = true ->
    In n0 (seq 0 (UserExpressions.evalIterator r cm sp)) ->
    In opu (Syntax.r_outputPattern r) ->
    UserExpressions.evalOutputPatternUnit opu cm sp n0 = Some a ->
    In a (modelElements (execute t cm)).
Proof.
  intros. 
  apply Certification.tr_execute_in_elements.
  exists sp. split ; [assumption | ].
  apply Certification.tr_instantiateOnPiece_in. (* FIXME : name incoherence *)
  exists r. 
  split.
  + apply Certification.tr_matchingRules_in. split ; assumption.
  + apply Certification.tr_instantiateRuleOnPiece_in.
    exists n0.
    split ; [ assumption | ].
    apply Certification.tr_instantiateIterationOnPiece_in.
    exists opu. split ; [ assumption | ].
    rewrite Certification.tr_instantiateElementOnPiece_leaf.
    assumption.
Qed.

Lemma destruct_in_modelLinks_execute_lem {MM1} {T1} {T2} {BEQ} :
  forall 
  {t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ))}
     {l}
     {m},
    In l (modelLinks (execute t m)) ->
    exists sp r n p te,
      In sp (allTuples t m) 
      /\ In r (Syntax.rules t) 
      /\ UserExpressions.evalGuard r m sp = true
      /\ In n (seq 0 (UserExpressions.evalIterator r m sp))
      /\ In p (Syntax.r_outputPattern r) 
      /\ UserExpressions.evalOutputPatternUnit p m sp n = return te
      /\ In l (UserExpressions.evalOutputPatternLink m sp te n (RichTraceLink.drop(traceTrOnModel t m)) p).

Proof.
  intros.
  destruct_in_modelLinks_execute H IN_E. 
  destruct_apply_pattern H IN_RULE.  
  destruct_applyRuleOnPiece H IN_IT IN_APP_PAT. 
  destruct_applyIterationOnPiece IN_APP_PAT H_IN_OUTPAT.   
  destruct_in_matchingRules IN_RULE H_MATCH_RULE.
  unfold applyUnitOnPiece in IN_APP_PAT.
  PropUtils.destruct_match IN_APP_PAT ; [ | ListUtils.unfold_In_cons IN_APP_PAT ].
  eauto 15.
Qed.


Ltac simpl_accessors_any H :=
  repeat first [ ConcreteSyntax.simpl_cr_accessors H 
        | ConcreteSyntax.simpl_elem_accessors H 
        | ConcreteSyntax.simpl_link_accessors H
        | Syntax.simpl_r_accessors H 
        | Syntax.simpl_opu_accessors H]. 

Ltac progress_in_In_rules H :=
  match type of H with 
    | In ?R (Syntax.rules _) =>
        simpl Syntax.rules in H ;
        progress repeat unfold_In_cons H ;
        subst R
  end.


Ltac exploit_evaloutpat H :=
  match type of H with 

  | UserExpressions.evalOutputPatternUnit _ _ _ (Parser.parseOutputPatternUnit _) = Some _ =>
      unfold Parser.parseOutputPatternUnit in H ;
      exploit_evaloutpat H (* recursion *)
       
  | UserExpressions.evalOutputPatternUnit _ _ _ _ = Some _ =>
      simpl in H ;
      ConcreteExpressions.inv_makeElement H
  end.

Ltac unfold_parseRule H :=
  match type of H with
    | context[Parser.parseRule (ConcreteSyntax.Build_ConcreteRule _ _ _ _ _ )] => unfold Parser.parseRule in H

    | context[Parser.parseRule ?E] =>
        (* For the case where a rule is defined 
           outside the transformation. *) 
        unfold E in H ; 
        unfold_parseRule H (* recursion *)

    | context[Parser.parseRule _] => 
        fail "Cannot read the rule"

    | _ => 
        fail "Cannot find something to unfold (Parser.parseRule)"
  end.

Ltac progress_in_In_outpat H :=
  match type of H with 
    | context[Parser.parseRule _] => 
        unfold_parseRule H ;
        progress_in_In_outpat H (* recursion *)
                      
    | In ?opu (Syntax.r_outputPattern (Syntax.buildRule _ _ _ _)) =>
        unfold Syntax.r_outputPattern in H ; 
        unfold ConcreteSyntax.r_outpat in H ;
        unfold List.map in H ;
        progress repeat unfold_In_cons H ;
        subst opu 
            
  end.

Ltac exploit_in_it H :=
  match type of H with
    | context[Parser.parseRule _] => 
        unfold_parseRule H ;
        exploit_in_it H (* recursion *)

    | In ?I (seq _ (UserExpressions.evalIterator (Syntax.buildRule _ _ _ _ ) _ _)) => 
      unfold UserExpressions.evalIterator in H ; 
      unfold Syntax.r_iterator in H ; 
      unfold ConcreteSyntax.r_iter in H ;
      simpl seq in H ;
      repeat unfold_In_cons H ;
      subst I
  end.
  
Ltac exploit_evalGuard H :=
    match type of H with
      | context[Parser.parseRule _] => 
         unfold_parseRule H ;
         exploit_evalGuard H (* recursion *)

      | UserExpressions.evalGuard (Syntax.buildRule _ _ _ _) _ _ = true => 
          unfold UserExpressions.evalGuard in H ; 
          unfold Syntax.r_guard in H ; 
          unfold ConcreteSyntax.r_guard in H ; 
          unfold ConcreteSyntax.r_InKinds in H ; 
          ConcreteExpressions.inv_makeGuard H
      
    end.

(** Tactics foor the user (BW) *)
Ltac exploit_element_in_result H :=
  match type of H with
  | In _ (modelElements (execute _ _)) =>
      
      let r := fresh "r" in
      let sp := fresh "sp" in
      let n := fresh "n" in
      let opu := fresh "opu" in
      let IN_ELTS := fresh "IN_ELTS" in
      let IN_RULE := fresh "IN_RULE" in
      let MATCH_GUARD := fresh "MATCH_GUARD" in
      let IN_IT := fresh "IN_IT" in
      let IN_OP := fresh "IN_OP" in
      let EV := fresh "EV" in
            
      (* (1) *)
      destruct (Tactics.destruct_in_modelElements_execute_lem H)
      as (r & sp & n & opu & IN_ELTS & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & EV) ;
      
      (* (2) *)
      (* Case analysis on the rule that has matched. *)
      Tactics.progress_in_In_rules IN_RULE ;

      (* (_) *) 
      (* Consider the fact that the guard was true. *)
      Tactics.exploit_evalGuard MATCH_GUARD ; 

      (* (_) *)
      Tactics.exploit_in_it IN_IT ;
      
      (* (_) *) 
      (* Make the ouput-pattern-element appear. *)
      Tactics.progress_in_In_outpat IN_OP ;
        
      (* (_) *)
      (* Make the matched element appear *)
      Tactics.exploit_evaloutpat EV ;
      
      (* (7) *)
      Semantics.exploit_in_allTuples IN_ELTS
  end. 

Ltac unfold_parseOutputPatternUnit H :=
    unfold Parser.parseOutputPatternUnit in H ;
    unfold Parser.parseOutputPatternLinks in H ;
    unfold Parser.parseOutputPatternLink in H ;
    repeat ConcreteSyntax.simpl_elem_accessors H.
  
Ltac unfold_evalOutputPatternLink H :=
    unfold UserExpressions.evalOutputPatternLink in H ;
    ConcreteSyntax.simpl_cr_accessors H ;
    Syntax.simpl_opu_accessors H.

Ltac exploit_in_eval_link H :=
    match type of H with
    | In _ (UserExpressions.evalOutputPatternLink _ _ _ _ _ (Parser.parseOutputPatternUnit _ _)) => 
        let TMP := fresh "TMP" in
        let pl := fresh "pl" in
        let IN := fresh "IN" in
        let l := fresh "l" in
        unfold_parseOutputPatternUnit H ; 
        unfold_evalOutputPatternLink H ;
        unfold Parser.dropToList in H ;
        rewrite optionListToList_Some in H ;
        apply in_flat_map in H ; destruct H as (pl, (TMP, H)) ;
        repeat ListUtils.unfold_In_cons TMP; 
        subst pl ;
        apply OptionListUtils.in_optionListToList in H ; 
        destruct H as (l & H & IN) ;
        ConcreteExpressions.inv_makeLink H ;
          apply in_singleton in IN 
    end.


Ltac exploit_link_in_result H :=
  match type of H with
  | In _ (modelLinks (execute _ _)) =>
      
      let r := fresh "r" in
      let sp := fresh "sp" in
      let n := fresh "n" in
      let opu := fresh "opu" in
      let te := fresh "te" in
      let IN_ELTS := fresh "IN_ELTS" in
      let IN_RULE := fresh "IN_RULE" in
      let MATCH_GUARD := fresh "MATCH_GUARD" in
      let IN_IT := fresh "IN_IT" in
      let IN_OP := fresh "IN_OP" in
      let EV := fresh "EV" in
      let IN_L := fresh "IN_L" in
            
      (* (1) *)
      destruct (Tactics.destruct_in_modelLinks_execute_lem H)
      as (sp & r & n & opu & te & IN_ELTS & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & EV & IN_L) ;
      
      (* (2) *)
      (* Case analysis on the rule that has matched. *)
      Tactics.progress_in_In_rules IN_RULE ;

      (* (_) *) 
      (* Consider the fact that the guard was true. *)
      Tactics.exploit_evalGuard MATCH_GUARD ; 

      (* (_) *)
      Tactics.exploit_in_it IN_IT ;
      
      (* (_) *) 
      (* Make the ouput-pattern-element appear. *)
      Tactics.progress_in_In_outpat IN_OP ;
        
      (* (_) *)
      (* Make the matched element appear *)
      Tactics.exploit_evaloutpat EV ;
      
      (* (7) *)
      Semantics.exploit_in_allTuples IN_ELTS ;

      Tactics.exploit_in_eval_link IN_L  
  end. 


Ltac exploit_in_trace H :=
  let se := fresh "se" in
  let r := fresh "r" in
  let i := fresh "i" in
  let e := fresh "e" in
  let te := fresh "te" in
  let IN_SOURCE := fresh "IN_SOURCE" in
  let IN_RULE := fresh "IN_RULE" in
  let MATCH_GUARD := fresh "MATCH_GUARD" in
  let IN_IT := fresh "IN_IT" in
  let IN_OUTPATP := fresh "IN_OUTPAT" in
  let EQ := fresh "EQ" in
  let EV := fresh "EV" in

 
  destruct (destruct_in_trace_lem H) 
    as (se & r & i & e & te & IN_SOURCE & IN_RULE & MATCH_GUARD & IN_IT & IN_OUTPAT & EQ & EV);
  
  (* 2 *)
  progress_in_In_rules IN_RULE ;
  
  (* _ *)
  exploit_evalGuard MATCH_GUARD  ; 

  (* _ *)
  exploit_in_it IN_IT ;

  (* 3 *)
  progress_in_In_outpat IN_OUTPAT ;

  (* 5 *) 
  exploit_evaloutpat EV ; 

  (* (7) *)
  (* not useful here *)
  Semantics.in_allTuples_auto.


(** Tactics to progress in the goal (not in the hypothesis) *)

Ltac destruct_in_trace_G :=
  match goal with 
    [ |- In _ (traceTrOnModel _ _)] => 
      unfold traceTrOnModel ;
      apply in_flat_map
  end.


(** Forward Descriptions *)

Lemma transform_elements_fw {tc} cm p tp (t:Syntax.Transformation (tc:=tc)) :
  In p (allTuples t cm) ->
  In tp (elements_proj (traceTrOnPiece t cm p)) ->
  In tp (modelElements (execute t cm)).
Proof.
  intros IN1 IN2.
  simpl.
  unfold traceTrOnModel.
  rewrite map_flat_map.
  apply List.in_flat_map.
  eauto.
Qed.

(* Used in Class2Relational *)
Lemma transform_element_fw {tc} cm e te (t:Syntax.Transformation (tc:=tc)) :
  0 < Syntax.arity t ->
  In e (modelElements cm) ->
  In te (elements_proj (traceTrOnPiece t cm [e])) ->
  In te (modelElements (execute t cm)).
Proof.
  intros A IN1 IN2.
  eapply Tactics.allModelElements_allTuples in IN1 ; [ | exact A].
  eapply transform_elements_fw ; eauto.
Qed.


Lemma in_links_fw tc cm (t:Syntax.Transformation (tc:=tc)):
  forall (sp:InputPiece) (r:Syntax.Rule) i opu produced_element,

    incl sp (modelElements cm) ->
    
    Datatypes.length sp <= Syntax.arity t ->
    
    In r t.(Syntax.rules)  ->
    
    UserExpressions.evalGuard r cm sp = true ->
    
    In i (seq 0 (UserExpressions.evalIterator r cm sp)) ->
    
    In opu (Syntax.r_outputPattern r) ->
    
    UserExpressions.evalOutputPatternUnit opu cm sp i = Some produced_element ->
    
    
    forall l,
      In l  (UserExpressions.evalOutputPatternLink cm sp produced_element i (RichTraceLink.drop(traceTrOnModel t cm)) opu) ->
      In l (modelLinks (execute t cm)).
Proof.
  intros sp r i opu produced_element.
  intros IN_MOD A IN_R EVAL_GUARD  EVAL_IT IN_OPU  EVAL_OUT_EL EVAL_OUT_LINK. 
  intro INLV.

  apply Certification.tr_execute_in_links.

  exists sp.  
  split.
  {
    apply Certification.allTuples_incl_length.
    exact IN_MOD.
    exact A.
  }
  {
    apply Certification.tr_applyOnPiece_in.
    exists r.
    split.
    {
      apply Certification.tr_matchingRules_in.
      split.
      { exact IN_R. }
      { exact EVAL_GUARD. }
    }
    {
      apply Certification.tr_applyRuleOnPiece_in.
      exists i.
      split.
      { exact EVAL_IT. }
      { 
        apply Certification.tr_applyIterationOnPiece_in.
        exists opu.
        split.
        { exact IN_OPU. }
        { 
          rewrite Certification.tr_applyUnitOnPiece_leaf with (te:=produced_element).
          { exact INLV. }
          { exact EVAL_OUT_EL. }
        }
      }
    }
  }
Qed.
