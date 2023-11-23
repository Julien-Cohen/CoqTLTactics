Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import TransformationConfiguration.
Require Import UserExpressions.

Require Import RichTraceLink.

Notation elements_proj := (map RichTraceLink.produced).

Section Semantics.

Context {tc: TransformationConfiguration}.

(** * Pattern matching *)

Definition allTuples (tr: Transformation) (sm : SourceModel) : list InputPiece :=
  tuples_up_to_n sm.(modelElements) tr.(arity).

Definition matchingRules (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list Rule :=
  filter (fun (r:Rule) => evalGuard r sm sp) tr.(rules).



(** * Building traces *)

Definition traceElementOnPiece (o: OutputPatternUnit) (sm: SourceModel) (sp: InputPiece) (iter: nat)
  : option TraceLink :=
  match (evalOutputPatternUnit o sm sp iter) with
  | Some e => Some 
                {| source := (sp, iter, o.(opu_name)) ;
                  produced :=  e ;
                  linkPattern := o.(opu_link) |}
  | None => None
  end.

Definition traceIterationOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) :  Trace :=
  flat_map (fun o => optionToList (traceElementOnPiece o sm sp iter))
    r.(r_outputPattern).

Definition traceRuleOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) : Trace :=
  flat_map (traceIterationOnPiece r sm sp)
    (seq 0 (evalIterator r sm sp)).

Definition traceTrOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : Trace :=
  flat_map (fun r => traceRuleOnPiece r sm sp) (matchingRules tr sm sp).



Definition compute_trace (tr: Transformation) (sm : SourceModel) :  RichTraceLink.Trace :=
  flat_map (traceTrOnPiece tr sm) (allTuples tr sm).  


(** * Apply link part of the r.h.s of rules (uses traces) **)

Definition applyTrOnModel (sm : SourceModel) (tls:Trace): list TargetLinkType :=
  flat_map 
    (fun lk => lk.(linkPattern) (drop tls) (getIteration lk) sm (getSourcePiece lk) lk.(produced)) 
    tls. 




(** * Execute **)


Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  let t := compute_trace tr sm
  in
  {|
    modelElements := elements_proj t ;
    modelLinks := applyTrOnModel sm t
  |}.

End Semantics.



(** * Some tactics *)

(* tactics need to be outside the section to be visible *)


Ltac exploit_in_allTuples H :=
  match type of H with 
    In _ (allTuples _ _) => 
      unfold allTuples in H ; 
      apply tuples_up_to_n_incl in H ;
      ListUtils.incl_inv H
  end.

Ltac in_allTuples_auto :=
  match goal with 
    [ H : In _ (allTuples _ _) |- _ ] =>
       exploit_in_allTuples H
  end.


