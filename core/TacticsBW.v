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

Import Metamodel Model.

Ltac progress_in_In_rules H :=
  match type of H with 
    | In ?R (Syntax.rules _) =>
        simpl Syntax.rules in H ;
        progress repeat ListUtils.unfold_In_cons H ; (* generates one goal for each rule to consider *)
        subst R
  end.


Ltac exploit_evalOutputPatternUnit H :=
  match type of H with 

(*  | UserExpressions.evalOutputPatternUnit _ _ _ (Parser.parseOutputPatternUnit _) = Some _ =>
      autounfold with parse in H ;
      exploit_evalOutputPatternUnit H (* recursion *)*)

  | ConcreteExpressions.makeElement _ _ _ _ _ _ = Some _ => 
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
        autounfold with ConcreteRule_accessors ConcreteOutputPatternUnit_accessors parse in H ;
        unfold Syntax.r_outputPattern in H ; 
        unfold List.map in H ;
        progress repeat unfold_In_cons H ;
        first [PropUtils.inj H | discriminate H (* useful ? *) ] (*subst opu*) 
            
  end.

Ltac exploit_In_evalIterator H :=
  autounfold with tracelink in  H ;
  match type of H with
    | context[Parser.parseRule _] => 
        unfold_parseRule H ;
        exploit_In_evalIterator H (* recursion *)

    | In ?I (seq _ (UserExpressions.evalIterator (Syntax.buildRule _ _ _ _ ) _ _)) => 
      unfold UserExpressions.evalIterator in H ; 
      unfold Syntax.r_iterator in H ; 
      unfold ConcreteSyntax.r_iter in H ;
      simpl seq in H ;
      repeat unfold_In_cons H ;
      try (is_var I ; subst I)
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


Ltac unfold_parseOutputPatternUnit H :=
  autounfold with parse in H ;
  autounfold with ConcreteOutputPatternUnit_accessors in H.

Ltac exploit_In_apply_link H :=
  match type of H with 
    In _ (Semantics.apply_link_pattern (Semantics.compute_trace _ _) _ _) =>
      let TMP := fresh "TMP" in
      let pl := fresh "pl" in
      let IN := fresh "IN" in
      let l := fresh "l" in
      unfold Semantics.apply_link_pattern in H ;
      autounfold with tracelink parse in H ;

      unfold Parser.dropToList in H ;

      repeat match type of H with 
        In _ (_ ++ _) => apply in_app_or in H ; destruct H as [H | H] 
      | In _ (OptionListUtils.optionListToList (Some _)) => rewrite OptionListUtils.optionListToList_Some in H
      | In _ nil => solve[inversion H]
      | In _ (OptionListUtils.optionListToList _) => apply OptionListUtils.in_optionListToList in H ; destruct H as (l & H & IN)
      end  ;
      ConcreteExpressions.inv_makeLink H ;
repeat match goal with [IN : List.In _ (_::_) |- _ ] => ListUtils.unfold_In_cons IN | [IN : List.In _ nil |- _] => solve[inversion IN] end  ;
      try PropUtils.inj IN
  end.
    
Ltac destruct_source H :=
  match type of H with
  | In {| PoorTraceLink.source := (_,_,_) |} _ => idtac
  | In {| PoorTraceLink.source := ?S |} _ => is_var S ; destruct S as ((?&?)&?)
  | In {| RichTraceLink.source := (_,_,_) |} _ => idtac
  | In {| RichTraceLink.source := ?S |} _ => is_var S ; destruct S as ((?&?)&?)
  end.



(** * Tactics for the user *)

(** Pivot tactic on traces *)
Ltac exploit_in_trace H :=
  match type of H with 
   | In ?A (compute_trace _ _) => 
      let se := fresh "se" in
      let r := fresh "r" in
      let i := fresh "i" in
      let opu := fresh "opu" in
      let IN_ELTS := fresh "IN_ELTS" in
      let IN_RULE := fresh "IN_RULE" in
      let MATCH_GUARD := fresh "MATCH_GUARD" in
      let IN_IT := fresh "IN_IT" in
      let IN_OUTPAT := fresh "IN_OUTPAT" in
      let EV := fresh "EV" in

      try destruct_source H ; 
  
      (* 1 : inversion *)
      apply -> Semantics.in_compute_trace_inv_alt_alt_alt in H ;
      autounfold with tracelink in H ;
      destruct H as (IN_ELTS & _ & r & IN_RULE & MATCH_GUARD & IN_IT & opu & IN_OUTPAT & EV); (* the _ because there is no information here *)
  
      (* 2 : case analysis on the rules in the transformation *)
      progress_in_In_rules IN_RULE (* one sub-goal per rule *) ;
      
      (* 3 : get rid of the rules that cannot match *)
      exploit_evalGuard MATCH_GUARD  ; 

      (* 4.a : unify the iteration number *)
      exploit_In_evalIterator IN_IT  ;

      (* 4.b : unify the out-pattern with those of the selected rule *)
      progress_in_In_outpat IN_OUTPAT ;

      (* 4.c : unify te and the evaluation of the out-pattern *)
      exploit_evalOutputPatternUnit EV  ;

      (* 4.d : destruct incl to In *)
      repeat ListUtils.explicit_incl IN_ELTS 

      (* CHECK-ME : Remark : 4.a, 4.b, 4.c and 4.d are independant ; they can be switched *)

                         
  | In _ (RichTraceLink.drop (compute_trace _ _)) => 
      (* when poor traces are concerned, we lift them to rich traces and try again *)
      RichTraceLink.lift H ;
      autounfold with tracelink in H ;
      exploit_in_trace H (* recursion *)
                       
  end.


(** Two tactics for user that rely on the pivot tactic above. *)
Ltac exploit_element_in_result IN :=
  let H := fresh "H" in
  let tk := fresh "tk" in
  let p := fresh "p" in
  
  (* make the trace appear *)
  apply -> Semantics.in_modelElements_inv in IN ;
  destruct IN as (tk & H & IN) ;
  destruct tk as [? p ?] ;
  unfold RichTraceLink.produced in H ; subst p ; [] ;

  (* exploit the trace *)
  exploit_in_trace IN.


Ltac exploit_link_in_result IN :=
  let IN_L := fresh "IN_L" in
  let tk := fresh "tk" in
  let p := fresh "p" in

  (* make the trace appear *)
  apply -> Semantics.in_modelLinks_inv in IN ;
  destruct IN as (tk & IN & IN_L) ;
  destruct tk as [? ? ?]  ;
  
  (* exploit the trace *)
  exploit_in_trace IN ;

  exploit_In_apply_link IN_L.
