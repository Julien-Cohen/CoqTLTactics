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


Definition matchPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) : list Rule :=
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
  flat_map (fun r => instantiateRuleOnPattern r sm sp) (matchPattern tr sm sp).

Definition instantiateRuleOnPatternIterName (r: Rule) (sm: SourceModel) (sp: list SourceElementType) (iter: nat) (name: string): option (TargetElementType) :=
  match (Rule_findOutputPatternElement r name) with
  | Some o =>  instantiateElementOnPattern o sm sp iter
  | None => None
  end.

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
  flat_map (fun r => traceRuleOnPattern r sm sp) (matchPattern tr sm sp).


Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceElementType) :=
  tuples_up_to_n sm.(modelElements) tr.(arity).

Definition trace (tr: Transformation) (sm : SourceModel) : list TraceLink :=
  flat_map (tracePattern tr sm) (allTuples tr sm).  

Definition resolveIter (tls: list TraceLink) (sm: SourceModel) (name: string)
            (sp: list SourceElementType)
            (iter : nat) : option TargetElementType :=
  match find (source_compare (sp,iter,name)) tls with
  | Some tl' => Some (tl'.(target))
  | None => None
  end.

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
  match sp with 
  | Some sp' => resolve tr sm name sp'
  | None => None
  end.

Definition maybeResolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
  (sp: option (list (list SourceElementType))) : option (list TargetElementType) :=
  match sp with 
  | Some sp' => resolveAll tr sm name sp'
  | None => None
  end.

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
  flat_map (fun r => applyRuleOnPattern r tr sm sp) (matchPattern tr sm sp).

(** * Execute **)

Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  {|
    modelElements := flat_map (instantiatePattern tr sm) (allTuples tr sm) ;
    modelLinks := flat_map (applyPattern tr sm) (allTuples tr sm)
  |}.

End Semantics.
