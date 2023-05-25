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
      to [
        ELEM "s" ::: Mealy.StateClass  
          << fun _ _ s => BuildState (Moore.State_getName s) >>
          
      ];

      rule "transition"
      from [Moore.TransitionClass]
      to [
        ELEM "t" ::: Mealy.TransitionClass
          << fun _ m t => BuildTransition 
                          (Moore.Transition_getInput t)
                          (value (option_map Moore.State_getOutput (Moore.Transition_getTarget t m))) >> 
          <<<
             LINK  
              Mealy.TransitionSourceReference //
              (fun tls _ m moore_tr mealy_tr =>
                maybeBuildTransitionSource mealy_tr
                  (maybeResolve tls "s" Mealy.StateClass 
                    (maybeSingleton (Moore.Transition_getSourceObject moore_tr m)))) ;
            LINK 
              Mealy.TransitionTargetReference //
              (fun tls _ m moore_tr mealy_tr =>
                maybeBuildTransitionTarget mealy_tr
                  (maybeResolve tls "s" Mealy.StateClass 
                    (maybeSingleton (Moore.Transition_getTargetObject moore_tr m)))) 
          >>>
      ]
].

Definition Moore2Mealy := parse Moore2Mealy'.

Close Scope coqtl.

