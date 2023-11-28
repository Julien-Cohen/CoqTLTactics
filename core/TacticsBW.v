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



(* This is a corollary of in_compute_trace_inv. *)
(* Used only 1 time. *)
(* REMOVE-ME *)
Corollary destruct_in_modelLinks_execute_lem {MM1} {T1} {T2} {BEQ} :
  forall 
  {t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ))}
     {l}
     {m},
    In l (modelLinks (execute t m)) ->
    exists s r n p te,
      In s (allTuples t m) (* fixme : improve this *)
      /\ In r (Syntax.rules t) 
      /\ UserExpressions.evalGuard r m s = true
      /\ In n (seq 0 (UserExpressions.evalIterator r m s))
      /\ In p (Syntax.r_outputPattern r) 
      /\ UserExpressions.evalOutputPatternUnit p m s n = return te
      /\ In l (UserExpressions.evalOutputPatternLink m s te n (RichTraceLink.drop(compute_trace t m)) p).

Proof.
  intros t l m H.
  apply Semantics.in_modelLinks_inv in H ; destruct H as (?&H&?).
  apply in_compute_trace_inv in H. 
  destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?).
  subst.
  repeat (first[eexists | split | eassumption]).
  (* improvement visible here *)  apply in_allTuples_incl ; auto.
Qed.


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



Local Ltac unfold_parseOutputPatternUnit H :=
    unfold Parser.parseOutputPatternUnit in H ;
    unfold Parser.parseOutputPatternLinks in H ;
    unfold Parser.parseOutputPatternLink in H ;
    repeat ConcreteSyntax.simpl_elem_accessors H.
  
Local Ltac unfold_evalOutputPatternLink H :=
    unfold UserExpressions.evalOutputPatternLink in H ;
    ConcreteSyntax.simpl_cr_accessors H ;
    Syntax.simpl_opu_accessors H.

Local Ltac exploit_in_eval_link H :=
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

(** Tactic for the user *)

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
      destruct (destruct_in_modelLinks_execute_lem H)
      as (sp & r & n & opu & te & IN_ELTS & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & EV & IN_L) ;
      
      (* (2) *)
      (* Case analysis on the rule that has matched. *)
      progress_in_In_rules IN_RULE ;

      (* (_) *) 
      (* Consider the fact that the guard was true. *)
      exploit_evalGuard MATCH_GUARD ; 

      (* (_) *)
      exploit_in_it IN_IT ;
      
      (* (_) *) 
      (* Make the ouput-pattern-element appear. *)
      progress_in_In_outpat IN_OP ;
        
      (* (_) *)
      (* Make the matched element appear *)
      exploit_evaloutpat EV ;
      
      (* (7) *)
      Semantics.exploit_in_allTuples IN_ELTS ;

      (* (8) *)
      exploit_in_eval_link IN_L  
  end. 

Ltac explicit_incl H :=
  match type of H with
  | incl (_::_) _ =>
      let H1 := fresh H in
      apply incl_cons_inv in H ; destruct H as (H1 & H)
  |  incl nil _ => clear H
  end.

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
  
      apply Semantics.in_compute_trace_inv in H ;

      destruct H as (se & IN_ELTS & A & r & IN_RULE & MATCH_GUARD & i & IN_IT & opu & IN_OUTPAT & te & EQ & EV);
  
      (* 2 *)
      progress_in_In_rules IN_RULE (* one sub-goal per rule *) ;
      
      (* _ *)
      TacticsBW.exploit_evalGuard MATCH_GUARD  ; 
      
      (* _ *)
      TacticsBW.exploit_in_it IN_IT ;
      
      (* 3 *)
      progress_in_In_outpat IN_OUTPAT ;
      
      (* 5 *) 
      exploit_evaloutpat EV ;
      
      (* ??? *)
      repeat explicit_incl IN_ELTS ;

      (* ??? *)
      try inj EQ ; try discriminate
                         
  | In _ (RichTraceLink.drop (compute_trace _ _)) => 
      (* when poor traces are concerned, we lift them to rich traces and try again *)
      RichTraceLink.lift H ;
      exploit_in_trace H (* recursion *)
                       
  end.

Ltac exploit_element_in_result IN :=
  let H := fresh "H" in
  let tk := fresh "tk" in
  let p := fresh "p" in
  apply -> Semantics.in_modelElements_inv in IN ;
  destruct IN as (tk & H & IN) ;
  destruct tk as [? p ?] ;
  unfold RichTraceLink.produced in H ; subst p ; [] ;
  exploit_in_trace IN.
