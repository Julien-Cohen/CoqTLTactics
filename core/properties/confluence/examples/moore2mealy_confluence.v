
Require Import String.
Require Import EqNat.
Require Import List.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.


Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.properties.confluence.basic.basicExpressions.
Require Import core.properties.confluence.basic.basicSemantics.
Require Import core.properties.confluence.basic.basicSyntax.
Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.Certification.
Require Import core.utils.Utils.
Require Import core.modeling.ModelingTransformationConfiguration.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import transformations.Moore2Mealy.Moore.
Require Import transformations.Moore2Mealy.Mealy.

#[export]
Instance Moore2MealyTransformationConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration MooreMetamodel_Metamodel_Instance MealyMetamodel_Metamodel_Instance.

#[export]  
Instance Moore2MealyModelingTransformationConfiguration : ModelingTransformationConfiguration Moore2MealyTransformationConfiguration :=
 Build_ModelingTransformationConfiguration Moore2MealyTransformationConfiguration MooreMetamodel_ModelingMetamodel_Instance MealyMetamodel_ModelingMetamodel_Instance.

Open Scope coqtl.


Definition Moore2Mealy :=
  buildTransformation 1
    [
      buildRule "transition"
        (fun m t => Some true)
        (fun m t => Some 1)
        nil;
      buildRule "state"
        (fun m s => Some false)
        (fun m s => Some 1)
        nil
    ].

  
Definition Moore2Mealy2 :=
  buildTransformation 1
    [
      buildRule "state"
        (fun m s => Some false)
        (fun m s => Some 1)
        nil;
      buildRule "transition"
        (fun m t => Some true)
        (fun m t => Some 1)
        nil
    ].

Close Scope coqtl.

