Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Scheme Equality for list.

Class EqDec (A : Type) :=
  { eqb : A -> A -> bool ; }.

Section Semantics.

  Context {SourceModelElement SourceModelLink: Type}.
  Context {eqdec_sme: EqDec SourceModelElement}.
  Context {TargetModelElement TargetModelLink: Type}.
  Context (SourceModel := Model SourceModelElement SourceModelLink).
  Context (TargetModel := Model TargetModelElement TargetModelLink).
  Context (Transformation := @Transformation SourceModelElement SourceModelLink TargetModelElement TargetModelLink).

  Definition Expr (A: Type) (B: Type) : Type := A -> B.

  Definition evalExpr {A B:Type} (f: Expr A B) (a: A) := f a. 

  Definition evalGuardExpr' (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
    evalExpr (@Rule_getGuardExpr SourceModelElement SourceModelLink TargetModelElement TargetModelLink r) sm sp.

  Definition evalIteratorExpr (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) :
    nat :=
    match (evalExpr (@Rule_getIteratorExpr SourceModelElement SourceModelLink TargetModelElement TargetModelLink r) sm sp) with
    | Some n => n
    | _ => 0
    end.

  Definition evalOutputPatternElementExpr (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (o: OutputPatternElement)
    : option TargetModelElement := 
    (evalExpr (@OutputPatternElement_getElementExpr SourceModelElement SourceModelLink TargetModelElement TargetModelLink o) iter sm sp).

  Definition evalOutputPatternLinkExpr
             (sm: SourceModel) (sp: list SourceModelElement) (oe: TargetModelElement) (iter: nat) (tr: list TraceLink)
             (o: OutputPatternElementReference)
    : option TargetModelLink :=
    (evalExpr (@OutputPatternElementReference_getLinkExpr SourceModelElement SourceModelLink TargetModelElement TargetModelLink o) tr iter sm sp oe).

  (** * Instantiate **)

  Definition matchRuleOnPattern (r: Rule) (sm : SourceModel) (sp: list SourceModelElement) : bool :=
    match evalGuardExpr' r sm sp with Some true => true | _ => false end.

  Definition matchPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list Rule :=
    filter (fun (r:Rule) => matchRuleOnPattern r sm sp) (Transformation_getRules tr).

  Definition instantiateElementOnPattern (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat)
    : option TargetModelElement :=
    evalOutputPatternElementExpr sm sp iter o.

  Definition instantiateIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) :  list TargetModelElement :=
    flat_map (fun o => optionToList (instantiateElementOnPattern o sm sp iter))
      (Rule_getOutputPatternElements r).

  Definition instantiateRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) :  list TargetModelElement :=
    flat_map (instantiateIterationOnPattern r sm sp)
      (indexes (evalIteratorExpr r sm sp)).

  Definition instantiatePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TargetModelElement :=
    flat_map (fun r => instantiateRuleOnPattern r sm sp) (matchPattern tr sm sp).

  Definition instantiateRuleOnPatternIterName (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (name: string): option (TargetModelElement) :=
    match (Rule_findOutputPatternElement r name) with
    | Some o =>  instantiateElementOnPattern o sm sp iter
    | None => None
    end.

  (** * Trace **)

  Definition traceElementOnPattern (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat)
    : option TraceLink :=
    match (instantiateElementOnPattern o sm sp iter) with
    | Some e => Some (buildTraceLink (sp, iter, OutputPatternElement_getName o) e)
    | None => None
    end.

  Definition traceIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) :  list TraceLink :=
    flat_map (fun o => optionToList (traceElementOnPattern o sm sp iter))
      (Rule_getOutputPatternElements r).

  Definition traceRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) :  list TraceLink :=
    flat_map (traceIterationOnPattern r sm sp)
      (indexes (evalIteratorExpr r sm sp)).

  Definition tracePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TraceLink :=
    flat_map (fun r => traceRuleOnPattern r sm sp) (matchPattern tr sm sp).

  Definition maxArity (tr: Transformation) : nat := Transformation_getArity tr.

  Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (allModelElements sm) (maxArity tr).

  Definition trace (tr: Transformation) (sm : SourceModel) : list TraceLink :=
    flat_map (tracePattern tr sm) (allTuples tr sm).  

  Definition TraceLink' := @TraceLink SourceModelElement TargetModelElement.

(* users are required to do a filter on tls: all tls in the result need to satisfy:
   (list_beq SourceModelElement beq_ModelElement (TraceLink_getSourcePattern tl) sp)  *)

  Definition resolveIter' (tls: list TraceLink') (sm: SourceModel) (name: string)
             (sp: list SourceModelElement)
             (iter : nat) : option TargetModelElement :=
  let tl := find (fun tl: TraceLink => 
    ((TraceLink_getIterator tl) =? iter) &&
    ((TraceLink_getName tl) =? name)%string) tls in
  match tl with
    | Some tl' => Some (TraceLink_getTargetElement tl')
    | None => None
  end.

  Definition resolve' (tr: list TraceLink) (sm: SourceModel) (name: string)
    (sp: list SourceModelElement) : option TargetModelElement :=
    resolveIter' tr sm name sp 0.

  Definition resolveAllIter' (tr: list TraceLink) (sm: SourceModel) (name: string)
    (sps: list(list SourceModelElement)) (iter: nat)
    : option (list TargetModelElement) :=
    Some (flat_map (fun l:(list SourceModelElement) => optionToList (resolveIter' tr sm name l iter)) sps).

  Definition resolveAll' (tr: list TraceLink) (sm: SourceModel) (name: string)
    (sps: list(list SourceModelElement)) : option (list TargetModelElement) :=
    resolveAllIter' tr sm name sps 0.
  
  Definition maybeResolve' (tr: list TraceLink) (sm: SourceModel) (name: string)
    (sp: option (list SourceModelElement)) : option TargetModelElement :=
    match sp with 
    | Some sp' => resolve' tr sm name sp'
    | None => None
    end.

  Definition maybeResolveAll' (tr: list TraceLink) (sm: SourceModel) (name: string)
    (sp: option (list (list SourceModelElement))) : option (list TargetModelElement) :=
    match sp with 
    | Some sp' => resolveAll' tr sm name sp'
    | None => None
    end.


  (** * Apply **)

  Definition applyReferenceOnPattern
             (oper: OutputPatternElementReference)
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) (te: TargetModelElement) : option TargetModelLink :=
    evalOutputPatternLinkExpr sm sp te iter (trace tr sm) oper.

  Definition applyElementOnPattern
             (ope: OutputPatternElement)
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) : list TargetModelLink :=
    flat_map (fun oper => 
      match (evalOutputPatternElementExpr sm sp iter ope) with 
      | Some l => optionToList (applyReferenceOnPattern oper tr sm sp iter l)
      | None => nil
      end) (OutputPatternElement_getOutputElementReferences ope).

  Definition applyIterationOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : list TargetModelLink :=
    flat_map (fun o => applyElementOnPattern o tr sm sp iter)
      (Rule_getOutputPatternElements r).

  Definition applyRuleOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement): list TargetModelLink :=
    flat_map (applyIterationOnPattern r tr sm sp)
      (indexes (evalIteratorExpr r sm sp)).

  Definition applyPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list TargetModelLink :=
    flat_map (fun r => applyRuleOnPattern r tr sm sp) (matchPattern tr sm sp).

  (** * Execute **)

  Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
    Build_Model
      (* elements *) (flat_map (instantiatePattern tr sm) (allTuples tr sm))
      (* links *) (flat_map (applyPattern tr sm) (allTuples tr sm)).

End Semantics.
