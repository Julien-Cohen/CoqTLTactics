Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingMetamodel.

Class ModelingTransformationConfiguration (tc: TransformationConfiguration):= {

  smm: ModelingMetamodel SourceMetamodel;
  tmm: ModelingMetamodel TargetMetamodel;

  SourceEKind:= @EKind _ smm;
  SourceLKind:= @LKind _ smm;
  TargetEKind:= @EKind _ tmm;
  TargetLKind:= @LKind _ tmm;  

  denoteSourceEDatatype:= @denoteEDatatype _ smm; (* FIXME : not used *)
}.
