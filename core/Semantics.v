Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import TransformationConfiguration.
Require Import EvalUserExpressions.
Scheme Equality for list.


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
  match (evalOutputPatternElement o sm sp iter) with
  | Some e => Some {| source := (sp, iter, o.(opu_name)) ; produced :=  e |}
  | None => None
  end.

Definition traceIterationOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) :  list TraceLink :=
  flat_map (fun o => optionToList (traceElementOnPiece o sm sp iter))
    r.(r_outputPattern).

Definition traceRuleOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) :  list TraceLink :=
  flat_map (traceIterationOnPiece r sm sp)
    (seq 0 (evalIterator r sm sp)).

Definition traceTrOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list TraceLink :=
  flat_map (fun r => traceRuleOnPiece r sm sp) (matchingRules tr sm sp).



Definition traceTrOnModel (tr: Transformation) (sm : SourceModel) : list TraceLink :=
  flat_map (traceTrOnPiece tr sm) (allTuples tr sm).  


(** * Instantiate element part of the r.h.s. of rules *)

Definition instantiateRuleOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) :  list TargetElementType :=
  map produced (traceRuleOnPiece r sm sp).

Definition instantiateTrOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list TargetElementType :=
   map produced (traceTrOnPiece tr sm sp).

Definition instantiateTrOnModel (tr: Transformation) (sm : SourceModel) := flat_map (instantiateTrOnPiece tr sm) (allTuples tr sm).



(** * Apply link part of the r.h.s of rules (with traces) **)

Definition applyUnitOnPiece
            (opu: OutputPatternUnit)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: InputPiece) (iter: nat) : list TargetLinkType :=
  match (evalOutputPatternElement opu sm sp iter) with 
  | Some l => optionListToList (evalOutputPatternLink sm sp l iter (traceTrOnModel tr sm) opu)
  | None => nil
  end.

Definition applyIterationOnPiece (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: InputPiece) (iter: nat) : list TargetLinkType :=
  flat_map (fun o => applyUnitOnPiece o tr sm sp iter)
    r.(r_outputPattern).

Definition applyRuleOnPiece (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: InputPiece): list TargetLinkType :=
  flat_map (applyIterationOnPiece r tr sm sp)
    (seq 0 (evalIterator r sm sp)).

Definition applyTrOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list TargetLinkType :=
  flat_map (fun r => applyRuleOnPiece r tr sm sp) (matchingRules tr sm sp).

Definition applyTrOnModel (tr: Transformation) (sm : SourceModel) 
  : list TargetLinkType
  :=  flat_map (applyTrOnPiece tr sm) (allTuples tr sm).

(** * Execute **)


Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  {|
    modelElements := instantiateTrOnModel tr sm ;
    modelLinks := applyTrOnModel tr sm
  |}.

End Semantics.




Remark trace_duplicate_instantiate {tc :TransformationConfiguration} :
  forall tr sm,
    instantiateTrOnModel tr sm = List.map TraceLink.produced (traceTrOnModel tr sm).
Proof.
  intros tr sm. 
  unfold traceTrOnModel, instantiateTrOnModel. rewrite map_flat_map.
  apply flat_map_ext ; clear ; intro. 
  unfold instantiateTrOnPiece, traceTrOnPiece. rewrite map_flat_map.
  reflexivity.
Qed.



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
Lemma in_applyUnitOnPiece {A B C D E} :
  forall (tr:Transformation (tc:=Build_TransformationConfiguration A (Metamodel.Build_Metamodel B C D E))) 
         a opu sm sp it,
  In a (applyUnitOnPiece opu tr sm sp it) ->
  exists g, 
    evalOutputPatternElement opu sm sp it = Some g
    /\ In a (optionListToList (evalOutputPatternLink sm sp g it (traceTrOnModel tr sm) opu)).
Proof.  
  unfold applyUnitOnPiece.
  intros until it ; intro IN.
  PropUtils.destruct_match IN ; [ | contradiction IN].
  eauto.
Qed.


Ltac exploit_In_applyUnitOnPiece H NEWNAME :=
  match type of H with
    | In _ (applyUnitOnPiece _ _ _ _ _) =>
        apply in_applyUnitOnPiece in H ;
        destruct H as (? & (NEWNAME & H))
end.
