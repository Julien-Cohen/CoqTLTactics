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


(** * Tactics to deal with boolean equality on generated types. *)

(** (When we have generated a boolean equality function [eqb] on a type [T], [beq_eq_tac] proves that [forall (a:T) (b:T), eqb a b = true => a = b]. *)

Ltac basetype_eqb_eq_tac :=
  match goal with 
  | [ H : Nat.eqb    _ _ = true |- _ ] => apply EqNat.beq_nat_true in H ; subst 
  | [ H : Bool.eqb   _ _ = true |- _ ] => apply Bool.eqb_prop      in H ; subst 
  | [ H : beq_string _ _ = true |- _ ] => apply lem_beq_string_eq2 in H ; subst 
end.


Ltac composedtype_eqb_eq_tac :=
  match goal  with [ H : ?f ?a ?b = true |- _ ]  => unfold f in H  ; (* unfold the boolean equality function *)
  destruct a , b ; simpl in H end ;  
  destruct_conjunctions
.

Notation beq_is_eq f := (forall a b, f a b = true -> a = b).

Lemma lem_list_beq_eq {T} : 
  forall (f:T->T->bool),
    beq_is_eq f ->
    beq_is_eq (core.utils.ListUtils.list_beq f).
Proof.
  intros f C.
  induction a ; intro b ; destruct b ; simpl ; first [ discriminate | reflexivity | idtac ] ; [].
  intro E ; apply Bool.andb_true_iff in E ; destruct E.  
  f_equal ; [ apply C | apply IHa ] ; auto.
Qed.


Create HintDb beq_eq_database.
(* This HintDb is used by the [auto with] tactics below to uses lemmas on intermediate types that will be generated (and registered in the DB) *)

Ltac list_eqb_eq_tac :=
  match goal with
  | [ H : core.utils.ListUtils.list_beq _ _ _ = true |- _] => apply lem_list_beq_eq in H ; [ subst | solve[auto with beq_eq_database]]
  end.


Ltac beq_eq_tac :=
  let a := fresh "a" in
  let b := fresh "b" in
  let E := fresh "E" in
  intro a ; intro b ; intro E ;
  repeat first [ 
      basetype_eqb_eq_tac 
    | composedtype_eqb_eq_tac  
    | list_eqb_eq_tac
    ] ; 
  reflexivity 
.





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
      destruct H as [e [NEWNAME H]]                                           end.     

(* deprecated *)
Ltac destruct_execute :=
  match goal with 

    [ H : In _ ( (execute ?T _).(modelElements)) |- _ ] =>
      destruct_in_modelElements_execute H

    | [ H : In _ ( (execute ?T _).(modelLinks)) |- _ ] =>
        destruct_in_modelLinks_execute H
  end.


Ltac destruct_instantiateOnPiece H IN_MATCH_NEWNAME :=
  match type of H with 
    In _ (instantiateTrOnPiece ?T _ _) =>
      let e := fresh "r" in
      rewrite (core.Certification.tr_instantiateOnPiece_in T) in H ;
      destruct H as [e [IN_MATCH_NEWNAME H]]
  end.

Ltac destruct_instantiateOnPiece_auto :=
  match goal with 
    [ H : In _ (instantiateTrOnPiece ?T _ _) |- _ ] =>
      let H2 := fresh "IN_R" in
      let e := fresh "r" in
      destruct_instantiateOnPiece H H2
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
    In _ (instantiateRuleOnPiece _ _ _) =>
      let e := fresh "n" in
      rewrite (core.Certification.tr_instantiateRuleOnPiece_in) in H ;
      destruct H as [e [IN_IT_NEWNAME H]]
  end.

Ltac destruct_instantiateRuleOnPiece_auto :=
  match goal with 
    [ H : In _ (instantiateRuleOnPiece _ _ _) |- _ ] =>
      let H2 := fresh "IN_I" in
      destruct_instantiateRuleOnPiece H H2
  end.


Ltac destruct_instantiateIterationOnPiece H NEWNAME :=
  match type of H with 
    In _ (instantiateIterationOnPiece _ _ _ _) =>
      let e := fresh "opu" in
      apply core.Certification.tr_instantiateIterationOnPiece_in in H ;
      destruct H as [e [NEWNAME H]]
  end.
Ltac destruct_instantiateIterationOnPiece_auto :=
  match goal with 
    [ H : In _ (instantiateIterationOnPiece _ _ _ _) |- _ ] =>
      let H2 := fresh "IN_OP" in
      destruct_instantiateIterationOnPiece H H2
  end.


Ltac unfold_instantiateElementOnPiece H :=
  match type of H with 
    context[instantiateElementOnPiece _ _ _ _] => 
      rewrite core.Certification.tr_instantiateElementOnPiece_leaf in H 
  end.

Ltac unfold_instantiateElementOnPiece_auto :=
  match goal with 
    [ H : context[instantiateElementOnPiece _ _ _ _] |- _ ] => 
      unfold_instantiateElementOnPiece H 
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



Lemma destruct_in_trace_lem {MM1 : Metamodel} {T1} {T2} {BEQ1} {BEQ2} :
  forall
    {t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ1 BEQ2))} 
  {cm} {l},
  In l (traceTrOnModel t cm) ->
  exists p r i outpat te,   
    In p (allTuples t cm)
    /\ In r (Syntax.rules t) 
    /\ EvalUserExpressions.evalGuard r cm p = true 
    /\ In i (seq 0 (EvalUserExpressions.evalIterator r cm p))
    /\ In outpat (Syntax.r_outputPattern r)
    /\ l = {|
             TraceLink.source := (p, i, Syntax.opu_name outpat);
             TraceLink.produced := te
           |} 
    /\ EvalUserExpressions.evalOutputPatternElement outpat cm p i = return te .
Proof.
  intros.
  destruct_trace H ; 
  destruct_traceOnPiece H ; 
  destruct_traceRuleOnPiece H ; 
  destruct_traceIterationOnPiece H ; 
  destruct_in_optionToList H.
  Tactics.destruct_in_matchingRules IN0 M.
  unfold traceElementOnPiece in H.
 
  OptionUtils.monadInv H.
  unfold instantiateElementOnPiece in H.
  eauto 12.
Qed.

Corollary in_trace_in_models_source {MM1} {T1} {T2} {BEQ1} {BEQ2} :  
  forall (t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ1 BEQ2)))
 cm a b s i,
    In (TraceLink.buildTraceLink ([a],i,s) b ) (traceTrOnModel t cm) ->
    In a cm.(modelElements) .
Proof.
  intros t cm a b s i IN.

  (* 1 *)
  destruct (destruct_in_trace_lem IN) 
    as (se & r & n & e & te & IN_SOURCE & _ & _ & _ & _ & EQ & _).

  inj EQ.
 

  (* (7) *)
  Semantics.in_allTuples_auto.

  exact IN_SOURCE.
Qed.

Lemma in_trace_in_models_target {MM1:Metamodel} {T1} {T2} {BEQ1} {BEQ2} :
  forall 
    (t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ1 BEQ2)))
    cm a b,
     In (TraceLink.buildTraceLink a b) (traceTrOnModel t cm) ->
    In b (execute t cm).(modelElements).
Proof.
  intros t cm a b IN.
  destruct a as ((a & i) & s).

  (* 1 *) 
  destruct (destruct_in_trace_lem IN) 
    as (se & r & n & e & te & IN_SOURCE & IN_RULE & MATCH_GUARD & IN_IT & IN_OUTPAT & EQ & EV).
  
  inj EQ.
  simpl TraceLink.produced.

  unfold execute. 
  unfold modelElements.

  
  unfold instantiateTrOnPiece.
  apply in_flat_map.
  exists se ; split ; [ exact IN_SOURCE | ].

  apply in_flat_map.
  unfold matchingRules.
  exists r ;  split ; [ apply List.filter_In ; split ; assumption | ].

  unfold instantiateRuleOnPiece.
  apply in_flat_map.
  exists n ; split ; [ exact IN_IT | ].

  unfold instantiateIterationOnPiece.
  apply in_flat_map.
  exists e ; split ; [ exact IN_OUTPAT | ].

  unfold instantiateElementOnPiece. 
  unfold traceElementOnPiece.
  rewrite EV.
  compute ; auto.

Qed.


Lemma destruct_in_modelElements_execute_lem {MM1} {T1} {T2} {BEQ1} {BEQ2} :
  forall 
    {t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ1 BEQ2))} 
    {cm} {a},
    
  In a
    (modelElements (execute t cm)) ->
  exists r sp n0 opu,
    In sp (allTuples t cm)
    /\ In r (Syntax.rules t) 
    /\ EvalUserExpressions.evalGuard r cm sp = true 
    /\ In n0 (seq 0 (EvalUserExpressions.evalIterator r cm sp))
    /\ In opu (Syntax.r_outputPattern r) 
    /\ EvalUserExpressions.evalOutputPatternElement opu cm sp n0 =
         return a.
Proof.
  intros. 
  destruct_in_modelElements_execute H.  
  destruct_instantiateOnPiece H NEW1. 
  destruct_instantiateRuleOnPiece H NEW2. 
  destruct_instantiateIterationOnPiece H NEW3. 
  unfold_instantiateElementOnPiece H. 
  destruct_in_matchingRules NEW1 NEW4. 
  eauto 10.
Qed.


Lemma destruct_in_modelLinks_execute_lem {MM1} {T1} {T2} {BEQ1} {BEQ2} :
  forall 
  {t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ1 BEQ2))}
     {l}
     {m},
    In l (modelLinks (execute t m)) ->
    exists sp r n p te tls,
      In sp (allTuples t m) 
      /\ In r (Syntax.rules t) 
      /\ EvalUserExpressions.evalGuard r m sp = true
      /\ In n (seq 0 (EvalUserExpressions.evalIterator r m sp))
      /\ In p (Syntax.r_outputPattern r) 
      /\ EvalUserExpressions.evalOutputPatternElement p m sp n =
         return te
  
  /\ EvalUserExpressions.evalOutputPatternLink m sp te n (traceTrOnModel t m) p = return tls
  /\ In l tls.

Proof.
  intros.
  destruct_in_modelLinks_execute H IN_E. 
  destruct_apply_pattern H IN_RULE.  
  destruct_applyRuleOnPiece H IN_IT IN_APP_PAT. 
  destruct_applyIterationOnPiece IN_APP_PAT H_IN_OUTPAT.   
  destruct_in_matchingRules IN_RULE H_MATCH_RULE.
  unfold applyUnitOnPiece in IN_APP_PAT.
  PropUtils.destruct_match IN_APP_PAT ; [ | ListUtils.unfold_In_cons IN_APP_PAT ].
  ListUtils.destruct_in_optionListToList IN_APP_PAT.
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

  | EvalUserExpressions.evalOutputPatternElement _ _ _ (Parser.parseOutputPatternUnit _) = Some _ =>
      unfold Parser.parseOutputPatternUnit in H ;
      exploit_evaloutpat H (* recursion *)
       
  | EvalUserExpressions.evalOutputPatternElement _ _ _ _ = Some _ =>
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

    | In ?I (seq _ (EvalUserExpressions.evalIterator (Syntax.buildRule _ _ _ _ ) _ _)) => 
      unfold EvalUserExpressions.evalIterator in H ; 
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

      | EvalUserExpressions.evalGuard (Syntax.buildRule _ _ _ _) _ _ = true => 
          unfold EvalUserExpressions.evalGuard in H ; 
          unfold Syntax.r_guard in H ; 
          unfold ConcreteSyntax.r_guard in H ; 
          unfold ConcreteSyntax.r_InKinds in H ; 
          ConcreteExpressions.inv_makeGuard H
      
    end.


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
  In tp (instantiateTrOnPiece t cm p) ->
  In tp (modelElements (execute t cm)).
Proof.
  intros IN1 IN2.
  simpl.
  apply List.in_flat_map.
  eauto.
Qed.


Lemma transform_element_fw {tc} cm e te (t:Syntax.Transformation (tc:=tc)) :
  0 < Syntax.arity t ->
  In e (modelElements cm) ->
  In te (instantiateTrOnPiece t cm [e]) ->
  In te (modelElements (execute t cm)).
Proof.
  intros A IN1 IN2.
  eapply Tactics.allModelElements_allTuples in IN1 ; [ | exact A].
  eapply transform_elements_fw ; eauto.
Qed.


Lemma in_links_fw tc cm (t:Syntax.Transformation (tc:=tc)):
  forall (sp:Syntax.InputPiece) (r:Syntax.Rule) i opu produced_element produced_links,

    incl sp (modelElements cm) ->
    
    
    Datatypes.length sp <= Syntax.arity t ->
    
    In r t.(Syntax.rules)  ->
    
    EvalUserExpressions.evalGuard r cm sp = true ->
    
    In i (seq 0 (EvalUserExpressions.evalIterator r cm sp)) ->
    
    In opu (Syntax.r_outputPattern r) ->
    
    EvalUserExpressions.evalOutputPatternElement opu cm sp i = Some produced_element ->
    
    EvalUserExpressions.evalOutputPatternLink cm sp produced_element i (traceTrOnModel t cm) opu = Some produced_links ->
    
    forall l, In l  produced_links -> In l (modelLinks (execute t cm)).
Proof.
  intros sp r i opu produced_element produced_links.
  intros IN_MOD A IN_R EVAL_GUARD  EVAL_IT IN_OPU  EVAL_OUT_EL EVAL_OUT_LINK. 
  intros l INLV  .

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
          { 
            rewrite EVAL_OUT_LINK.
            simpl.
            exact INLV.
          }
          { exact EVAL_OUT_EL. }
        }
      }
    }
  }
Qed.
