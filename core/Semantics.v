Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import TransformationConfiguration.
Require Import EvalExpressions.
Scheme Equality for list.


Section Semantics.

Context {tc: TransformationConfiguration}.

(** * Pattern matching *)

Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceElementType) :=
  tuples_up_to_n sm.(modelElements) tr.(arity).

Definition matchingRules (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) : list Rule :=
  filter (fun (r:Rule) => evalGuardExpr r sm sp) tr.(rules).


(** * Instantiate element part of the r.h.s. of rules *)


Definition instantiateElementOnPattern : OutputPatternUnit -> SourceModel -> list SourceElementType -> nat -> option TargetElementType :=
  evalOutputPatternElementExpr.

Definition instantiateIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceElementType) (iter: nat) :  list TargetElementType :=
  flat_map (fun o => optionToList (instantiateElementOnPattern o sm sp iter))
    r.(r_outputPattern).

Definition instantiateRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceElementType) :  list TargetElementType :=
  flat_map (instantiateIterationOnPattern r sm sp)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition instantiateOnPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) : list TargetElementType :=
  flat_map (fun r => instantiateRuleOnPattern r sm sp) (matchingRules tr sm sp).



(** * Building traces *)

Definition traceElementOnPattern (o: OutputPatternUnit) (sm: SourceModel) (sp: list SourceElementType) (iter: nat)
  : option TraceLink :=
  match (instantiateElementOnPattern o sm sp iter) with
  | Some e => Some {| source := (sp, iter, o.(opu_name)) ; produced :=  e |}
  | None => None
  end.

Definition traceIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceElementType) (iter: nat) :  list TraceLink :=
  flat_map (fun o => optionToList (traceElementOnPattern o sm sp iter))
    r.(r_outputPattern).

Definition traceRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceElementType) :  list TraceLink :=
  flat_map (traceIterationOnPattern r sm sp)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition traceOnPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) : list TraceLink :=
  flat_map (fun r => traceRuleOnPattern r sm sp) (matchingRules tr sm sp).



Definition trace (tr: Transformation) (sm : SourceModel) : list TraceLink :=
  flat_map (traceOnPattern tr sm) (allTuples tr sm).  




(** * Apply link part of the r.h.s of rules (with traces) **)

Definition applyUnitOnPattern
            (opu: OutputPatternUnit)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: list SourceElementType) (iter: nat) : list TargetLinkType :=
  match (evalOutputPatternElementExpr opu sm sp iter) with 
  | Some l => optionListToList (evalOutputPatternLinkExpr sm sp l iter (trace tr sm) opu)
  | None => nil
  end.

Definition applyIterationOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceElementType) (iter: nat) : list TargetLinkType :=
  flat_map (fun o => applyUnitOnPattern o tr sm sp iter)
    r.(r_outputPattern).

Definition applyRuleOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceElementType): list TargetLinkType :=
  flat_map (applyIterationOnPattern r tr sm sp)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition applyOnPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) : list TargetLinkType :=
  flat_map (fun r => applyRuleOnPattern r tr sm sp) (matchingRules tr sm sp).

(** * Execute **)

Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  {|
    modelElements := flat_map (instantiateOnPattern tr sm) (allTuples tr sm) ;
    modelLinks := flat_map (applyOnPattern tr sm) (allTuples tr sm)
  |}.

End Semantics.

(** * Some tactics *)

(* tactics need to be outside the section to be visible *)


Ltac exploit_in_allTuples H :=
  match type of H with 
    In _ (allTuples _ _) => 
      unfold allTuples in H ; 
      apply tuples_up_to_n_incl in H ;
      incl_inv H
  end.

Ltac in_allTuples_auto :=
  match goal with 
    [ H : In _ (allTuples _ _) |- _ ] =>
       exploit_in_allTuples H
  end.

(** FIXME : move-me to Certification ? *)
Lemma in_applyUnitOnPattern {A B C D E} :
  forall (tr:Transformation (tc:=Build_TransformationConfiguration A (Metamodel.Build_Metamodel B C D E))) 
         a opu sm sp it,
  In a (applyUnitOnPattern opu tr sm sp it) ->
  exists g, 
    evalOutputPatternElementExpr opu sm sp it = Some g
    /\ In a (optionListToList (evalOutputPatternLinkExpr sm sp g it (trace tr sm) opu)).
Proof.  
  unfold applyUnitOnPattern.
  intros until it ; intro IN.
  PropUtils.destruct_match IN ; [ | contradiction IN].
  eauto.
Qed.


Ltac exploit_In_applyUnitOnPattern H NEWNAME :=
  match type of H with
    | In _ (applyUnitOnPattern _ _ _ _ _) =>
        apply in_applyUnitOnPattern in H ;
        destruct H as (? & (NEWNAME & H))
end.
