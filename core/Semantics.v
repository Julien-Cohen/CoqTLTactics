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

Definition allTuples (tr: Transformation) (sm : SourceModel) : list InputPiece :=
  tuples_up_to_n sm.(modelElements) tr.(arity).

Definition matchingRules (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list Rule :=
  filter (fun (r:Rule) => evalGuard r sm sp) tr.(rules).


(** * Instantiate element part of the r.h.s. of rules *)


Definition instantiateElementOnPiece : OutputPatternUnit -> SourceModel -> InputPiece -> nat -> option TargetElementType :=
  evalOutputPatternElement.

Definition instantiateIterationOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) :  list TargetElementType :=
  flat_map (fun o => optionToList (instantiateElementOnPiece o sm sp iter))
    r.(r_outputPattern).

Definition instantiateRuleOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) :  list TargetElementType :=
  flat_map (instantiateIterationOnPiece r sm sp)
    (seq 0 (evalIterator r sm sp)).

Definition instantiateOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list TargetElementType :=
  flat_map (fun r => instantiateRuleOnPiece r sm sp) (matchingRules tr sm sp).



(** * Building traces *)

Definition traceElementOnPiece (o: OutputPatternUnit) (sm: SourceModel) (sp: InputPiece) (iter: nat)
  : option TraceLink :=
  match (instantiateElementOnPiece o sm sp iter) with
  | Some e => Some {| source := (sp, iter, o.(opu_name)) ; produced :=  e |}
  | None => None
  end.

Definition traceIterationOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) :  list TraceLink :=
  flat_map (fun o => optionToList (traceElementOnPiece o sm sp iter))
    r.(r_outputPattern).

Definition traceRuleOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) :  list TraceLink :=
  flat_map (traceIterationOnPiece r sm sp)
    (seq 0 (evalIterator r sm sp)).

Definition traceOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list TraceLink :=
  flat_map (fun r => traceRuleOnPiece r sm sp) (matchingRules tr sm sp).



Definition trace (tr: Transformation) (sm : SourceModel) : list TraceLink :=
  flat_map (traceOnPiece tr sm) (allTuples tr sm).  




(** * Apply link part of the r.h.s of rules (with traces) **)

Definition applyUnitOnPiece
            (opu: OutputPatternUnit)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: InputPiece) (iter: nat) : list TargetLinkType :=
  match (evalOutputPatternElement opu sm sp iter) with 
  | Some l => optionListToList (evalOutputPatternLink sm sp l iter (trace tr sm) opu)
  | None => nil
  end.

Definition applyIterationOnPiece (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: InputPiece) (iter: nat) : list TargetLinkType :=
  flat_map (fun o => applyUnitOnPiece o tr sm sp iter)
    r.(r_outputPattern).

Definition applyRuleOnPiece (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: InputPiece): list TargetLinkType :=
  flat_map (applyIterationOnPiece r tr sm sp)
    (seq 0 (evalIterator r sm sp)).

Definition applyOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list TargetLinkType :=
  flat_map (fun r => applyRuleOnPiece r tr sm sp) (matchingRules tr sm sp).

(** * Execute **)

Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  {|
    modelElements := flat_map (instantiateOnPiece tr sm) (allTuples tr sm) ;
    modelLinks := flat_map (applyOnPiece tr sm) (allTuples tr sm)
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
Lemma in_applyUnitOnPiece {A B C D E} :
  forall (tr:Transformation (tc:=Build_TransformationConfiguration A (Metamodel.Build_Metamodel B C D E))) 
         a opu sm sp it,
  In a (applyUnitOnPiece opu tr sm sp it) ->
  exists g, 
    evalOutputPatternElement opu sm sp it = Some g
    /\ In a (optionListToList (evalOutputPatternLink sm sp g it (trace tr sm) opu)).
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
