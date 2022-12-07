Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingMetamodel.

Class ModelingTransformationConfiguration (tc: TransformationConfiguration):= {

  smmm: ModelingMetamodel SourceMetamodel;
  tmmm: ModelingMetamodel TargetMetamodel;

}.
