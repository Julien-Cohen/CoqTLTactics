Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.properties.confluence.basic.basicSyntax.
Require Import Bool.
Require Import Arith.
Require Import TransformationConfiguration.
Require Import core.properties.confluence.basic.basicExpressions.
Scheme Equality for list.


Section Semantics.

Context {tc: TransformationConfiguration}.

(** * Instantiate **)

Definition matchRuleOnPattern (r: Rule) (sm : SourceModel) (sp: list SourceElementType) : bool :=
  match evalGuardExpr r sm sp with Some true => true | _ => false end.

Definition matchPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) : list Rule :=
  filter (fun (r:Rule) => matchRuleOnPattern r sm sp) (Transformation_getRules tr).

Definition instantiateElementOnPattern (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceElementType) (iter: nat)
  : option TargetElementType :=
  evalOutputPatternElementExpr sm sp iter o.

Definition instantiateIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceElementType) (iter: nat) :  list TargetElementType :=
  flat_map (fun o => optionToList (instantiateElementOnPattern o sm sp iter))
    (Rule_getOutputPatternElements r).

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

Definition maxArity (tr: Transformation) : nat := Transformation_getArity tr.

Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceElementType) :=
  tuples_up_to_n sm.(modelElements) (maxArity tr).

Definition resolveIter (tr: Transformation) (sm: SourceModel) (name: string) (sp: list SourceElementType) (iter : nat) : option TargetElementType :=
let matchedRule := find (fun r:Rule => matchRuleOnPattern r sm sp) (Transformation_getRules tr) in
match matchedRule with
  | Some r =>  (instantiateRuleOnPatternIterName r sm sp iter name)
  | None => None
end.

(** * Apply **)

Definition applyElementOnPattern
            (ope: OutputPatternElement)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: list SourceElementType) (iter: nat) : list TargetLinkType :=
  match (evalOutputPatternElementExpr sm sp iter ope) with 
  | Some l => optionListToList (evalOutputPatternLinkExpr sm sp l (resolveIter tr) iter ope)
  | None => nil
  end.

Definition applyIterationOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceElementType) (iter: nat) : list TargetLinkType :=
  flat_map (fun o => applyElementOnPattern o tr sm sp iter)
    (Rule_getOutputPatternElements r).

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
