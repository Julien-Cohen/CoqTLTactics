Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingMetamodel.

Class ModelingTransformationConfiguration (tc: TransformationConfiguration):= {

  smmm: ModelingMetamodel tc.(SourceMetamodel);
  tmmm: ModelingMetamodel tc.(TargetMetamodel);

}.
