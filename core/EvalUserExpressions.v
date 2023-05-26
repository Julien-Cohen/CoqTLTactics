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



Definition evalGuard (r : Rule) (sm: SourceModel) (sp: InputPiece) : bool :=
  r.(r_guard) sm sp.

Definition evalIterator (r : Rule) (sm: SourceModel) (sp: InputPiece) :
  nat :=
  match r.(r_iterator) sm sp with
  | Some n => n
  | _ => 0
  end.

Definition evalOutputPatternElement (o: OutputPatternUnit) (sm: SourceModel) (sp: InputPiece) (iter: nat) 
  : option TargetElementType := 
  o.(opu_element) iter sm sp.

Definition evalOutputPatternLink
            (sm: SourceModel) (sp: InputPiece) (oe: TargetElementType) (iter: nat) (tra: list TraceLink)
            (o: OutputPatternUnit)
  : list TargetLinkType :=
  o.(opu_link) tra iter sm sp oe.

End Expressions.
