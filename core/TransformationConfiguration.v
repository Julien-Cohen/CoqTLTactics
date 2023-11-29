Require Import core.Model.
Require Import core.Metamodel.

Class TransformationConfiguration := {
  SourceMetamodel: Metamodel;
  TargetMetamodel: Metamodel;

  SourceElementType:= @ElementType SourceMetamodel;
  SourceLinkType:= @LinkType SourceMetamodel;

  TargetElementType:= @ElementType TargetMetamodel;
  TargetLinkType:= @LinkType TargetMetamodel;

  SourceModel := Model SourceMetamodel;
  TargetModel := Model TargetMetamodel;

  SourceElement_eqdec := @elements_eq_dec SourceMetamodel;
  TargetElement_eqdec := @elements_eq_dec TargetMetamodel;

  SourceElement_eqb := @elements_beq SourceMetamodel;
  TargetElement_eqb := @elements_beq TargetMetamodel;
}.


Notation InputPiece := (list SourceElementType).
