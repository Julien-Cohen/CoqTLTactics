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


Section Operational.

Context {tc: TransformationConfiguration}.



(** * Pattern matching *)

(* executable *)
Definition allTuples (tr: Transformation) (sm : SourceModel) : list InputPiece :=
  TupleUtils.tuples_up_to_n sm.(modelElements) tr.(arity).


(* executable *)
Definition matchingRules (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list Rule :=
  List.filter (fun (r:Rule) => evalGuard r sm sp) tr.(rules).



(** * Building traces *)

(* executable *)
Definition traceElementOnPiece (o: OutputPatternUnit) (sm: SourceModel) (sp: InputPiece) (iter: nat)
  : option TraceLink :=
    v <- evalOutputPatternUnit o sm sp iter ;
    return {| 
        source := (sp, iter, o.(opu_name)) ;
        produced := v ;
        linkPattern := o.(opu_link) 
      |}.



(* executable *)
Definition traceIterationOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) :  Trace :=
  flat_map
    (fun o => optionToList (traceElementOnPiece o sm sp iter))
    r.(r_outputPattern).



(* executable *)
Definition traceRuleOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) : Trace :=
  flat_map 
    (traceIterationOnPiece r sm sp)
    (seq 0 (evalIterator r sm sp)).



(* executable *)
Definition traceTrOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : Trace :=
  flat_map 
    (fun r => traceRuleOnPiece r sm sp) 
    (matchingRules tr sm sp).


(* executable *)
Definition compute_trace (tr: Transformation) (sm : SourceModel) :  TraceLink.Trace :=
  flat_map 
    (traceTrOnPiece tr sm) 
    (allTuples tr sm).  








(** * Apply link part of the r.h.s of rules (uses traces) **)

(* executable *)
Definition apply_link_pattern (tra:Trace) sm lk :list TargetLinkType := 
    lk.(linkPattern) (drop tra) (getIteration lk) sm (getSourcePiece lk) lk.(produced).





(* executable *)
Definition applyTrLkOnModel (sm : SourceModel) (tra:Trace): list TargetLinkType :=
    flat_map (apply_link_pattern tra sm) tra. 





(** * Execute **)

(* executable *)
Definition produced_elements := map TraceLink.produced.

(** Main definition below. *)

(* executable *)
Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  let t := compute_trace tr sm
  in
  {|
    modelElements := produced_elements t ;
    modelLinks := applyTrLkOnModel sm t
  |}.





End Operational.

  
