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

(* executable *)
Definition allTuples (tr: Transformation) (sm : SourceModel) : list InputPiece :=
  TupleUtils.tuples_up_to_n sm.(modelElements) tr.(arity).

(* predicative *)
Definition isTuple (sm : SourceModel) ip : Prop := 
  List.incl ip sm.(modelElements).

(* executable *)
Definition matchingRules (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list Rule :=
  List.filter (fun (r:Rule) => evalGuard r sm sp) tr.(rules).

(* predicative *)
Definition matchingRule (tr: Transformation) (sm : SourceModel) (sp: InputPiece) r : Prop :=
    List.In r tr.(rules) /\ UserExpressions.guard_ok r sm sp.

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

(* predicatif *)
Inductive traceElementOnPiece_rel (o: OutputPatternUnit) (sm: SourceModel) (sp: InputPiece) (iter: nat)
  : TraceLink -> Prop :=
    | r1 : forall v, evalOutputPatternUnit_rel o sm sp iter v ->
  traceElementOnPiece_rel o sm sp iter
     {| 
        source := (sp, iter, o.(opu_name)) ;
        produced := v ;
        linkPattern := o.(opu_link) 
      |}.

(* executable *)
Definition traceIterationOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) :  Trace :=
  flat_map
    (fun o => optionToList (traceElementOnPiece o sm sp iter))
    r.(r_outputPattern).

(* predicatif *)
Inductive traceIterationOnPiece_rel (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) (tl:TraceLink) : Prop :=
   | r2: forall o, 
        List.In o r.(r_outputPattern) ->
        traceElementOnPiece_rel o sm sp iter tl -> 
      traceIterationOnPiece_rel r sm sp iter tl.

(* executable *)
Definition traceRuleOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) : Trace :=
  flat_map 
    (traceIterationOnPiece r sm sp)
    (seq 0 (evalIterator r sm sp)).

(* predicatif *)
Inductive traceRuleOnPiece_rel (r: Rule) (sm: SourceModel) (sp: InputPiece) (tl:TraceLink) : Prop :=
  | r3 : 
    forall it, 
    evalIterator_rel r sm sp it ->
    traceIterationOnPiece_rel r sm sp it tl ->
    traceRuleOnPiece_rel r sm sp tl.

(* executable *)
Definition traceTrOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : Trace :=
  flat_map 
    (fun r => traceRuleOnPiece r sm sp) 
    (matchingRules tr sm sp).

(* predicatif *)
Inductive traceTrOnPiece_rel (tr: Transformation) (sm : SourceModel) (sp: InputPiece) (tl: TraceLink) : Prop :=
  | r4 : forall r, 
    traceRuleOnPiece_rel r sm sp tl ->
    matchingRule tr sm sp r ->
      traceTrOnPiece_rel tr sm sp tl.

(* executable *)
Definition compute_trace (tr: Transformation) (sm : SourceModel) :  TraceLink.Trace :=
  flat_map 
    (traceTrOnPiece tr sm) 
    (allTuples tr sm).  

(* predicatif *)
Inductive in_trace (tr: Transformation) (sm : SourceModel) (tl:TraceLink) : Prop :=
  | r5 : forall sp,
     traceTrOnPiece_rel tr sm sp tl ->
      isTuple sm sp ->
    in_trace tr sm tl .  


Definition is_trace trans sm tra : Prop :=
  forall lk, List.In lk tra <-> in_trace trans sm lk.    
(* On aurait pu définir ensemble en compréhension. *)


(** * Apply link part of the r.h.s of rules (uses traces) **)

(* executable *)
Definition apply_link_pattern (tls:Trace) sm lk :list TargetLinkType := 
    lk.(linkPattern) (drop tls) (getIteration lk) sm (getSourcePiece lk) lk.(produced).

 (* predicative *)
Definition apply_link_pattern_rel tls sm lk tl : Prop := 
   List.In tl (lk.(linkPattern) (drop tls) (getIteration lk) sm (getSourcePiece lk) lk.(produced)).
  

(* executable *)
Definition applyTrOnModel (sm : SourceModel) (tls:Trace): list TargetLinkType :=
    flat_map (apply_link_pattern tls sm) tls. 

(* predicative *)
Inductive applyTrOnModel_rel (sm : SourceModel) (tls:Trace) (tl: TargetLinkType) : Prop :=
 | r6 : forall lk, List.In lk tls -> 
    apply_link_pattern_rel tls sm lk tl -> 
    applyTrOnModel_rel sm tls tl. 




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
    modelLinks := applyTrOnModel sm t
  |}.


(* predicative *)
Inductive is_produced_element tr sm : TargetElementType -> Prop :=
    | r7 : forall a b c, 
        in_trace tr sm {| source := a; produced := b; linkPattern := c |} ->
        is_produced_element tr sm b.

Inductive is_produced_link tr sm (tl:TargetLinkType): Prop :=
    | r8 : forall tra, 
        is_trace tr sm tra ->
        applyTrOnModel_rel sm tra tl->
        is_produced_link tr sm tl.


Definition is_result tr sm tm: Prop :=
  (forall e, (List.In e tm.(modelElements) <-> is_produced_element tr sm e)) /\ 
  (forall lk, (List.In lk tm.(modelLinks) <-> is_produced_link tr sm lk)).
(* On aurait pu définir un ensemble en compréhension. *)


End Semantics.

  
