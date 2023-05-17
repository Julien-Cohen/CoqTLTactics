Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import TransformationConfiguration.
Scheme Equality for list.


Section Expressions.

Context {tc: TransformationConfiguration}.



Definition evalGuardExpr (r : Rule) (sm: SourceModel) (sp: list SourceElementType) : bool :=
  r.(r_guard) sm sp.

Definition evalIteratorExpr (r : Rule) (sm: SourceModel) (sp: list SourceElementType) :
  nat :=
  match r.(r_iterator) sm sp with
  | Some n => n
  | _ => 0
  end.

Definition evalOutputPatternElementExpr (o: OutputPatternUnit) (sm: SourceModel) (sp: list SourceElementType) (iter: nat) 
  : option TargetElementType := 
  o.(opu_elementExpr) iter sm sp.

Definition evalOutputPatternLinkExpr
            (sm: SourceModel) (sp: list SourceElementType) (oe: TargetElementType) (iter: nat) (tra: list TraceLink)
            (o: OutputPatternUnit)
  : option (list TargetLinkType) :=
  o.(opu_linkExpr) tra iter sm sp oe.

End Expressions.
