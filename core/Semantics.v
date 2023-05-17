Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import TransformationConfiguration.
Require Import Expressions.
Scheme Equality for list.


Section Semantics.

Context {tc: TransformationConfiguration}.

(** * Instantiate **)


Definition matchingRules (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) : list Rule :=
  filter (fun (r:Rule) => evalGuardExpr r sm sp) tr.(rules).

Definition instantiateElementOnPattern (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceElementType) (iter: nat)
  : option TargetElementType :=
  evalOutputPatternElementExpr sm sp iter o.

Definition instantiateIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceElementType) (iter: nat) :  list TargetElementType :=
  flat_map (fun o => optionToList (instantiateElementOnPattern o sm sp iter))
    r.(r_outputPattern).

Definition instantiateRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceElementType) :  list TargetElementType :=
  flat_map (instantiateIterationOnPattern r sm sp)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition instantiatePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) : list TargetElementType :=
  flat_map (fun r => instantiateRuleOnPattern r sm sp) (matchingRules tr sm sp).


(* Definition instantiateRuleOnPatternIterName (r: Rule) (sm: SourceModel) (sp: list SourceElementType) (iter: nat) (name: string): option (TargetElementType) :=
  match (Rule_findOutputPatternElement r name) with
  | Some o =>  instantiateElementOnPattern o sm sp iter
  | None => None
  end.*)

(** * Trace **)

Definition traceElementOnPattern (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceElementType) (iter: nat)
  : option TraceLink :=
  match (instantiateElementOnPattern o sm sp iter) with
  | Some e => Some (buildTraceLink (sp, iter, o.(ope_name)) e)
  | None => None
  end.

Definition traceIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceElementType) (iter: nat) :  list TraceLink :=
  flat_map (fun o => optionToList (traceElementOnPattern o sm sp iter))
    r.(r_outputPattern).

Definition traceRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceElementType) :  list TraceLink :=
  flat_map (traceIterationOnPattern r sm sp)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition tracePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) : list TraceLink :=
  flat_map (fun r => traceRuleOnPattern r sm sp) (matchingRules tr sm sp).


Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceElementType) :=
  tuples_up_to_n sm.(modelElements) tr.(arity).

Definition trace (tr: Transformation) (sm : SourceModel) : list TraceLink :=
  flat_map (tracePattern tr sm) (allTuples tr sm).  

Definition resolveIter (tls: list TraceLink) (sm: SourceModel) (name: string)
            (sp: list SourceElementType)
            (iter : nat) : option TargetElementType :=
  option_map target (find (source_compare (sp,iter,name)) tls) .

Definition resolve (tr: list TraceLink) (sm: SourceModel) (name: string)
  (sp: list SourceElementType) : option TargetElementType :=
  resolveIter tr sm name sp 0.


Definition resolveAllIter (tr: list TraceLink) (sm: SourceModel) (name: string)
  (sps: list(list SourceElementType)) (iter: nat)
  : option (list TargetElementType) :=
  Some (flat_map (fun l:(list SourceElementType) => optionToList (resolveIter tr sm name l iter)) sps).

Definition resolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
  (sps: list(list SourceElementType)) : option (list TargetElementType) :=
  resolveAllIter tr sm name sps 0.

Definition maybeResolve (tr: list TraceLink) (sm: SourceModel) (name: string)
  (sp: option (list SourceElementType)) : option TargetElementType :=
  sp' <- sp ;
  resolve tr sm name sp' .


Definition maybeResolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
  (sp: option (list (list SourceElementType))) : option (list TargetElementType) :=
  sp' <- sp ; 
  resolveAll tr sm name sp'.


(** * Apply **)

Definition applyElementOnPattern
            (ope: OutputPatternElement)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: list SourceElementType) (iter: nat) : list TargetLinkType :=
  match (evalOutputPatternElementExpr sm sp iter ope) with 
  | Some l => optionListToList (evalOutputPatternLinkExpr sm sp l iter (trace tr sm) ope)
  | None => nil
  end.

Definition applyIterationOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceElementType) (iter: nat) : list TargetLinkType :=
  flat_map (fun o => applyElementOnPattern o tr sm sp iter)
    r.(r_outputPattern).

Definition applyRuleOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceElementType): list TargetLinkType :=
  flat_map (applyIterationOnPattern r tr sm sp)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition applyPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) : list TargetLinkType :=
  flat_map (fun r => applyRuleOnPattern r tr sm sp) (matchingRules tr sm sp).

(** * Execute **)

Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  {|
    modelElements := flat_map (instantiatePattern tr sm) (allTuples tr sm) ;
    modelLinks := flat_map (applyPattern tr sm) (allTuples tr sm)
  |}.

End Semantics.

(** Some tactics *)

(* tactics need to be outside the section to be visible *)
Ltac inv_maybeResolve H := 
  OptionUtils.monadInvN maybeResolve H.

Ltac inv_maybeResolveAll H := 
  OptionUtils.monadInvN maybeResolveAll H.


Ltac inv_resolve H :=
  match type of H with
  | resolve _ _ _ _ = Some _ =>
      unfold resolve in H ; 
      OptionUtils.monadInvN resolveIter H
  end.

Ltac progress_maybeResolve H :=
  match type of H with 
    maybeResolve _ _ _ _ = Some _ =>
      inv_maybeResolve H ;
      inv_resolve H ; 
      apply List.find_some in H ; 
      let N := fresh H in
      destruct H as (H & N)
end.

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
Lemma in_applyElementOnPattern {A B C D E} :
  forall (tr:Transformation (tc:=Build_TransformationConfiguration A (Metamodel.Build_Metamodel B C D E))) 
         a ope sm sp it,
  In a (applyElementOnPattern ope tr sm sp it) ->
  exists g, 
    evalOutputPatternElementExpr sm sp it ope = Some g
    /\ In a (optionListToList (evalOutputPatternLinkExpr sm sp g it (trace tr sm) ope)).
Proof.  
  unfold applyElementOnPattern.
  intros until it ; intro IN.
  PropUtils.destruct_match IN ; [ | contradiction IN].
  eauto.
Qed.


Ltac exploit_In_applyElementOnPattern H NEWNAME :=
  match type of H with
    | In _ (applyElementOnPattern _ _ _ _ _) =>
        apply in_applyElementOnPattern in H ;
        destruct H as (? & (NEWNAME & H))
end.
