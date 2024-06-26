From core
  Require 
   ConcreteExpressions 
   Parser 
   Semantics.

Import core.utils.Utils.
Import Model Semantics.

From usertools 
  Require 
   ConcreteExpressionTools 
   SemanticsTools
   SyntaxTools
   ConcreteSyntaxTools.

(** BW tactics for the user. The important tactics are the last three ones : one pivot tactics, one for elements that rely on the pivot, and one for links that also rely on the pivot tactic. *)


(** * Auxiliary BW tactics *)

Ltac In_rules_inv_tac H :=

  (* Precondition *)
  match type of H with 
    | In ?R (Syntax.rules _) =>

        (* Actions *)
        simpl Syntax.rules in H ;
        progress repeat ListUtils.unfold_In_cons H ; (* generate one goal for each rule to consider *)
        subst R
  end.


Ltac makeElement_inv_tac H :=

  (* Precondition *)
  match type of H with 
  | ConcreteExpressions.makeElement _ _ _ _ _ _ = Some _ => 

      (* Actions *)
      simpl in H ;
      ConcreteExpressionTools.inv_makeElement H
  end.


Ltac In_outputPattern_inv_tac H :=
  match type of H with 
    | context[Parser.parseRule _] => 
        autounfold with parse in H ;
        In_outputPattern_inv_tac H (* recursion *)
                      
    | In ?opu (Syntax.r_outputPattern (Syntax.buildRule _ _ _ _)) =>
        autounfold with 
         ConcreteRule_accessors ConcreteOutputPatternUnit_accessors parse rule_accessors in H ;
        unfold List.map in H ;
        progress repeat unfold_In_cons H ;
        first [PropUtils.inj H | discriminate H (* useful ? *) ] (*subst opu*)            
  end.


Ltac In_evalIterator_inv_tac H :=
  autounfold with tracelink in H ;
  match type of H with
    | context[Parser.parseRule _] => 
        autounfold with parse in H ;
        In_evalIterator_inv_tac H (* recursion *)

    | In ?I (seq _ (UserExpressions.evalIterator (Syntax.buildRule _ _ _ _ ) _ _)) => 
      unfold UserExpressions.evalIterator in H ; 
      autounfold with ConcreteRule_accessors rule_accessors in H ;
      simpl seq in H ;
      repeat unfold_In_cons H ;
      try (is_var I ; subst I)
  end.
  

Ltac evalGuard_inv_tac H :=
    match type of H with
      | context[Parser.parseRule _] => 
         autounfold with parse in H ;
         evalGuard_inv_tac H (* recursion *)

      | UserExpressions.evalGuard (Syntax.buildRule _ _ _ _) _ _ = true => 
          unfold UserExpressions.evalGuard in H ; 
          autounfold with ConcreteRule_accessors rule_accessors in H ; 
          ConcreteExpressionTools.inv_makeGuard H      
    end.



(* Explanation of the tactics below.
   Application of SemanticsTools.in_modelLinks_inv leaves an hypothesis with the following shape :
   [In l
     (apply_link_pattern 
       (compute_trace tr sm) 
       sm
       {|
         TraceLink.source := (s, i, n);
         TraceLink.produced := res;
         TraceLink.linkPattern := lp
       |}
      )
   ]   

The function [apply_link_pattern] there is the code that builds a new link, based on the user code [lp],  the computed trace, the source model, the source piece (pattern instance) and the  produced element). 

The tactic below unfolds all the engine mechanisms in the hypothesis until we can see the result of the application of the given [lp] user function. 
This tactics leaves the hypothesis for further manipulation after that. (In the general case, we do not know the form of the user code.)

*)
Ltac exploit_In_apply_link H :=

  (* Precondition *)
  match type of H with 
    In _ (Semantics.apply_link_pattern (Semantics.compute_trace _ _) _ _) =>
      
      (* local names *)
      let IN := fresh "IN" in
      let l := fresh "l" in

      (* Actions *)
      unfold Semantics.apply_link_pattern in H ;
      autounfold with tracelink parse in H ;
      unfold Parser.dropToList in H ;

      repeat 
        match type of H with 
        | In _ (_ ++ _) =>
            apply in_app_or in H ; 
            destruct H as [H | H] 
                            
        | In _ (OptionListUtils.optionListToList (Some _)) =>
            rewrite OptionListUtils.optionListToList_Some in H
        | In _ nil => 
            solve[inversion H]
                 
        | In _ (OptionListUtils.optionListToList _) => 
            apply OptionListUtils.in_optionListToList in H ;
            destruct H as (l & H & IN)
        end  ;
      
      ConcreteExpressionTools.inv_makeLink H ;
      
      repeat 
        match goal with 
        | [HIN : List.In _ (_::_) |- _ ] => ListUtils.unfold_In_cons HIN 
        | [HIN : List.In _ nil    |- _ ] => solve[inversion HIN] 
        end ;
      
      try PropUtils.inj IN
  end.
    

Ltac destruct_source H :=
  match type of H with
  | In {| PoorTraceLink.source := (_,_,_) |} _ => idtac
  | In {| PoorTraceLink.source := ?S |} _ => is_var S ; destruct S as ((?&?)&?)
  | In {| TraceLink.source := (_,_,_) |} _ => idtac
  | In {| TraceLink.source := ?S |} _ => is_var S ; destruct S as ((?&?)&?)
  end.



(** * Tactics for the user *)

(** Pivot tactic on traces *)
Ltac exploit_in_trace H :=

  (* Precondition *)
  match type of H with 
   | In _ (compute_trace _ _) => 

       (* local names *)
      let r := fresh "r" in
      let opu := fresh "opu" in
      let IN_ELTS := fresh "IN_ELTS" in
      let IN_RULE := fresh "IN_RULE" in
      let MATCH_GUARD := fresh "MATCH_GUARD" in
      let IN_IT := fresh "IN_IT" in
      let IN_OUTPAT := fresh "IN_OUTPAT" in
      let EV := fresh "EV" in

      
      try destruct_source H ; 
  
      (* 1: inversion *)
      apply  SemanticsTools.in_compute_trace_inv_right in H ;
      autounfold with tracelink in H ;
      destruct H 
        as (IN_ELTS & _ & r & IN_RULE & MATCH_GUARD 
            & IN_IT & opu & IN_OUTPAT & EV); 
      (* The _ because there is no information here *)
      try clear H ;

      (* 2: case analysis on the rules 
            in the transformation *)
      In_rules_inv_tac IN_RULE (* One sub-goal per rule *) ;
      
      (* 3: get rid of the rules that cannot match *)
      evalGuard_inv_tac MATCH_GUARD  ; 

      (* 4.a: unify the iteration number *)
      In_evalIterator_inv_tac IN_IT ; 

      (* 4.b.1 : unify the out-pattern with 
                 those of the selected rule *)
      In_outputPattern_inv_tac IN_OUTPAT ;

      (* 4.b.2 : unification with the evaluation of
                 the out-pattern *)
      makeElement_inv_tac EV ; 

      (* 4.c : destruct incl to In *)
      repeat ListUtils.explicit_incl IN_ELTS 

      (* Remark: 4.a, 4.b.(1-2) and 4.c are independant ;
                  they can be switched  (except 4.b.2 
                  that must occur after 4.b.1)           *)

  (* Precondition (second case) *) 
  | In _ (TraceLink.drop (compute_trace _ _)) => 
      (* When poor traces are concerned, 
         we lift them to rich traces and try again *)
      TraceLink.lift H ;
      autounfold with tracelink in H ;
      exploit_in_trace H (* recursion *)
                       
  end.


(** Two tactics for user, for elements and for links, 
    that rely on the pivot tactic. *)

Ltac exploit_element_in_result IN :=
  match type of IN with 
  | In _  (execute _ _).(modelElements) =>
      let s := fresh "s" in
      let i := fresh "i" in
      let n := fresh "n" in
      let p := fresh "p" in
      let IN_EXPL := fresh "IN_EXPL" in
      
      (* 1: make the trace appear *)
      apply -> SemanticsTools.in_modelElements_inv in IN ;
      destruct IN as (s & i & n & p & IN_EXPL) ;
      try clear IN ;
      
      (* 2: exploit the trace *)
      exploit_in_trace IN_EXPL
  end.


Ltac exploit_link_in_result IN :=
  match type of IN with 
  | In _ (execute _ _).(modelLinks) =>
      let IN_L := fresh "IN_L" in
      let IN_EXPL := fresh "IN_EXPL" in
  
      (* 1: make the trace appear *)
      apply -> SemanticsTools.in_modelLinks_inv in IN ;
      destruct IN as (? & ? & ? & ? & ? & IN_EXPL & IN_L) ;
      
      (* 2: exploit the trace *)
      exploit_in_trace IN_EXPL ;
      
      (* 3: exploit link creation code *)
      exploit_In_apply_link IN_L
  end.

