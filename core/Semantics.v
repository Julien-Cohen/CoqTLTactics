(** This module defines the behavior of the model transformation engine. *)

From core 
  Require
   utils.Utils 
   Model 
   Syntax 
   TransformationConfiguration 
   UserExpressions 
   TraceLink.

Import 
  NotationUtils
  OptionListUtils
  Model 
  Syntax 
  TransformationConfiguration 
  UserExpressions 
  TraceLink.


Section Semantics.

Context {tc: TransformationConfiguration}.

(** * Pattern matching *)

Definition allTuples (tr: Transformation) (sm : SourceModel) : list InputPiece :=
  TupleUtils.tuples_up_to_n sm.(modelElements) tr.(arity).

Definition matchingRules (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list Rule :=
  List.filter (fun (r:Rule) => evalGuard r sm sp) tr.(rules).



(** * Building traces *)

Definition traceElementOnPiece (o: OutputPatternUnit) (sm: SourceModel) (sp: InputPiece) (iter: nat)
  : option TraceLink :=
    v <- evalOutputPatternUnit o sm sp iter ;
    return {| 
        source := (sp, iter, o.(opu_name)) ;
        produced := v ;
        linkPattern := o.(opu_link) 
      |}.

Definition traceIterationOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) :  Trace :=
  flat_map
    (fun o => optionToList (traceElementOnPiece o sm sp iter))
    r.(r_outputPattern).

Definition traceRuleOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) : Trace :=
  flat_map 
    (traceIterationOnPiece r sm sp)
    (seq 0 (evalIterator r sm sp)).

Definition traceTrOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : Trace :=
  flat_map 
    (fun r => traceRuleOnPiece r sm sp) 
    (matchingRules tr sm sp).

Definition compute_trace (tr: Transformation) (sm : SourceModel) :  TraceLink.Trace :=
  flat_map 
    (traceTrOnPiece tr sm) 
    (allTuples tr sm).  

    



(** * Apply link part of the r.h.s of rules (uses traces) **)

Definition apply_link_pattern tls sm lk := 
    lk.(linkPattern) (drop tls) (getIteration lk) sm (getSourcePiece lk) lk.(produced).
  

Definition applyTrOnModel (sm : SourceModel) (tls:Trace): list TargetLinkType :=
    flat_map (apply_link_pattern tls sm) tls. 




(** * Execute **)

Definition produced_elements := map TraceLink.produced.

(** Main definition below. *)

Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  let t := compute_trace tr sm
  in
  {|
    modelElements := produced_elements t ;
    modelLinks := applyTrOnModel sm t
  |}.




End Semantics.

  
