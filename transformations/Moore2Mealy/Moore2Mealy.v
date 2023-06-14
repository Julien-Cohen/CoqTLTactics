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
  Build_TransformationConfiguration Metamodel_Instance MealyMetamodel_Metamodel_Instance.

#[export]  
Instance Moore2MealyModelingTransformationConfiguration : ModelingTransformationConfiguration Moore2MealyTransformationConfiguration :=
 Build_ModelingTransformationConfiguration Moore2MealyTransformationConfiguration ModelingMetamodel_Instance MealyMetamodel_ModelingMetamodel_Instance.

Open Scope coqtl.

Definition Moore2Mealy' :=
    transformation
    [
      rule "state"
      from [Moore.State_K]
      to [
        ELEM "s" ::: Mealy.State_K  
          << fun _ _ s => BuildState s.(Moore.name) >>
          
      ];

      rule "transition"
      from [Moore.Transition_K]
      to [
        ELEM "t" ::: Mealy.Transition_K
          << fun _ m t => BuildTransition 
                          t.(Moore.input)
                          (value (option_map Moore.output (Moore.Transition_getTarget t m))) >> 
          <<<
             LINK  
              Mealy.TransitionSource_K //
              (fun tls _ m moore_tr mealy_tr =>
                maybeBuildTransitionSource mealy_tr
                  (maybeResolve tls "s" Mealy.State_K 
                    (maybeSingleton (Moore.Transition_getSourceObject moore_tr m)))) ;
            LINK 
              Mealy.TransitionTarget_K //
              (fun tls _ m moore_tr mealy_tr =>
                maybeBuildTransitionTarget mealy_tr
                  (maybeResolve tls "s" Mealy.State_K 
                    (maybeSingleton (Moore.Transition_getTargetObject moore_tr m)))) 
          >>>
      ]
].

Definition Moore2Mealy := parse Moore2Mealy'.

Close Scope coqtl.

