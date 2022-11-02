Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import transformations.Moore2Mealy.Moore.
Require Import transformations.Moore2Mealy.Mealy.
Require Import transformations.Moore2Mealy.MooreSemantics.


Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

#[export]
Instance Moore2MealyTransformationConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration MooreMetamodel_Metamodel_Instance MealyMetamodel_Metamodel_Instance.

#[export]  
Instance Moore2MealyModelingTransformationConfiguration : ModelingTransformationConfiguration Moore2MealyTransformationConfiguration :=
 Build_ModelingTransformationConfiguration Moore2MealyTransformationConfiguration MooreMetamodel_ModelingMetamodel_Instance MealyMetamodel_ModelingMetamodel_Instance.

Open Scope coqtl.

Definition Moore2Mealy' :=
    transformation
    [
      rule "state"
      from [Moore.StateClass]
      where (fun m s => 
              negb (existsb (Moore.beq_State s) 
                       (optionList2List (map 
                          (fun tr => Moore.Transition_getTarget tr m)
                          (MooreMetamodel_allTransitions m)))))
      to [
        elem [Moore.StateClass] Mealy.StateClass "s"
          (fun _ _ s => BuildState (Moore.State_getName s)) nil
      ]
].

Definition Moore2Mealy := parse Moore2Mealy'.

Close Scope coqtl.

  