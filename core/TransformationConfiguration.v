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

  SourceElement_eqdec := @elements_eqdec SourceMetamodel;
  TargetElement_eqdec := @elements_eqdec TargetMetamodel;

  SourceElement_eqb := @elements_eqdec SourceMetamodel;
  TargetElement_eqb := @elements_eqdec TargetMetamodel;
}.
