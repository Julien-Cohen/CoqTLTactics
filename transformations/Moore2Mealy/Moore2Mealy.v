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

Import Glue.

#[export]
Instance Moore2MealyTransformationConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration Moore.MM Mealy.MM.

#[export]  
Instance Moore2MealyModelingTransformationConfiguration : ModelingTransformationConfiguration Moore2MealyTransformationConfiguration :=
 Build_ModelingTransformationConfiguration Moore2MealyTransformationConfiguration Moore.MMM Mealy.MMM.

Open Scope coqtl.

Definition Moore2Mealy' :=
    transformation
    [
      rule "state"
      from [Moore.State_K]
      to [
        ELEM "s" ::: Mealy.State_K  
          << fun _ _ s => 
            {| 
              State_id := s.(Moore.State_id) 
            |} >>
          
      ];

      rule "transition"
      from [Moore.Transition_K]
      to [
        ELEM "t" ::: Mealy.Transition_K
          << fun _ m t =>
            {|
              Transition_id := t.(Moore.Transition_id) ;
              Transition_input := t.(Moore.Transition_input) ;
              Transition_output := (value (option_map Moore.State_output (Moore.getTransition_target m t))) 
            |} >> 
          
        LINK ::: Mealy.Transition_source_K 
          << fun tls _ m moore_tr mealy_tr =>
            try t_source := Moore.Transition_getSourceObject moore_tr m
             in
             try res := resolve tls "s" Mealy.State_K (singleton t_source) 
                in glue mealy_tr with res >> ;
            
        LINK ::: Mealy.Transition_target_K 
          << fun tls _ m moore_tr mealy_tr =>
            try t_target := Moore.Transition_getTargetObject moore_tr m
             in
             try res := resolve tls "s" Mealy.State_K (singleton t_target)
              in 
              glue mealy_tr with res 
          >>
      ]
].

Definition Moore2Mealy := parse Moore2Mealy'.

Close Scope coqtl.

