Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingMetamodel.

Class ModelingTransformationConfiguration (tc: TransformationConfiguration):= {

  smm: ModelingMetamodel SourceMetamodel;
  tmm: ModelingMetamodel TargetMetamodel;

}.
