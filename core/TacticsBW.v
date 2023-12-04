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



Local Ltac simpl_accessors_any H :=
  repeat first [ ConcreteSyntax.simpl_cr_accessors H 
        | ConcreteSyntax.simpl_elem_accessors H 
        | ConcreteSyntax.simpl_link_accessors H
        | Syntax.simpl_r_accessors H 
        | Syntax.simpl_opu_accessors H]. 

Local Ltac progress_in_In_rules H :=
  match type of H with 
    | In ?R (Syntax.rules _) =>
        simpl Syntax.rules in H ;
        progress repeat unfold_In_cons H ;
        subst R
  end.


Local Ltac exploit_evaloutpat H :=
  match type of H with 

  | UserExpressions.evalOutputPatternUnit _ _ _ (Parser.parseOutputPatternUnit _) = Some _ =>
      unfold Parser.parseOutputPatternUnit in H ;
      exploit_evaloutpat H (* recursion *)
       
  | UserExpressions.evalOutputPatternUnit _ _ _ _ = Some _ =>
      simpl in H ;
      ConcreteExpressions.inv_makeElement H
  end.

Local Ltac unfold_parseRule H :=
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


Local Ltac progress_in_In_outpat H :=
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




Ltac explicit_incl H :=
  match type of H with
  | incl (_::_) _ =>
      let H1 := fresh H in
      apply incl_cons_inv in H ; destruct H as (H1 & H)
  |  incl nil _ => clear H
  end.



Local Ltac unfold_parseOutputPatternUnit H :=
    unfold Parser.parseOutputPatternUnit in H ;
    unfold Parser.parseOutputPatternLinks in H ;
    unfold Parser.parseOutputPatternLink in H ;
    repeat ConcreteSyntax.simpl_elem_accessors H.

Local Ltac unfold_evalOutputPatternLink H :=
    unfold UserExpressions.evalOutputPatternLink in H.

Local Ltac exploit_in_eval_link H :=
  match type of H with 
    In _ (apply_link_pattern (compute_trace _ _) _ _) =>
      let TMP := fresh "TMP" in
      let pl := fresh "pl" in
      let IN := fresh "IN" in
      let l := fresh "l" in
      unfold apply_link_pattern in H ;
      unfold RichTraceLink.getSourcePiece, RichTraceLink.linkPattern, RichTraceLink.getIteration, RichTraceLink.produced, RichTraceLink.source in H ;
      unfold_parseOutputPatternUnit H ; 
      unfold_evalOutputPatternLink H ;
      unfold Parser.dropToList in H ;
      rewrite optionListToList_Some in H ;
      apply in_flat_map in H ; destruct H as (pl, (TMP, H)) ;
      repeat ListUtils.unfold_In_cons TMP ; 
      subst pl ;
      apply OptionListUtils.in_optionListToList in H ; 
      destruct H as (l & H & IN) ;
      ConcreteExpressions.inv_makeLink H ;
      unfold ConcreteSyntax.o_outpat in H ;
      apply in_singleton in IN ;
      try first [discriminate IN | inj IN]
  end.
    


(** * Tactics for the user *)

(** Pivot tactic on traces *)
Ltac exploit_in_trace H :=
  match type of H with 
  | In _ (compute_trace _ _) => 
      let se := fresh "se" in
      let r := fresh "r" in
      let i := fresh "i" in
      let opu := fresh "opu" in
      let te := fresh "te" in
      let A := fresh "A" in
      let IN_ELTS := fresh "IN_ELTS" in
      let IN_RULE := fresh "IN_RULE" in
      let MATCH_GUARD := fresh "MATCH_GUARD" in
      let IN_IT := fresh "IN_IT" in
      let IN_OUTPATP := fresh "IN_OUTPAT" in
      let EQ := fresh "EQ" in
      let EV := fresh "EV" in
  
      (* 1 *)
      apply Semantics.in_compute_trace_inv in H ;
      destruct H as (se & IN_ELTS & _ & r & IN_RULE & MATCH_GUARD & i & IN_IT & opu & IN_OUTPAT & te & EQ & EV); (* the _ because there is no information here *)
  
      (* 2 *)
      progress_in_In_rules IN_RULE (* one sub-goal per rule *) ;
      
      (* 3 : get rid of the rules that cannot match *)
      exploit_evalGuard MATCH_GUARD  ; 

      (* 4.a : unify the iteration number *)
      exploit_in_it IN_IT ;

      (* 4.b : unify the out-pattern with those of the selected rule *)
      progress_in_In_outpat IN_OUTPAT ;

      (* 4.c : unify te and the evaluation of the out-pattern *)
      exploit_evaloutpat EV ;

      (* 4.d : destruct incl to In *)
      repeat explicit_incl IN_ELTS ;

      (* Remark : 4.a, 4.b, 4.c and 4.d are independant ; they can be switched *)

      (* 5.a *) 
      try inj EQ ; 

      (* 5.b *) 
      try discriminate

      (* Remark :  5.a and 5.b must occur after 4.a, 4.b and 4.c. Also, 5.a and 5.b can be switched *) 
      
                         
  | In _ (RichTraceLink.drop (compute_trace _ _)) => 
      (* when poor traces are concerned, we lift them to rich traces and try again *)
      RichTraceLink.lift H ;
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
  let H := fresh "H" in
  let tk := fresh "tk" in
  let p := fresh "p" in

  (* make the trace appear *)
  apply -> Semantics.in_modelLinks_inv in IN ;
  destruct IN as (tk & IN & IN_L) ;
  destruct tk as [? ? ?]  ;
  
  (* exploit the trace *)
  exploit_in_trace IN ;

  exploit_in_eval_link IN_L.
