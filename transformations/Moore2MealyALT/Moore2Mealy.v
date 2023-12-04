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

Require Import transformations.Moore2MealyALT.Moore.
Require Import transformations.Moore2MealyALT.Mealy.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

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
           fun _ _ s => 
	    return 
            {|
              State_id := s.(Moore.State_id) 
            |} 
          
      ];

      rule "transition"
      from [Moore.Transition_K]
      to [
        ELEM "t" ::: Mealy.Transition_K
           fun _ m t => 
            return {|
              Transition_source := t.(Moore.Transition_source) ;
              Transition_input := t.(Moore.Transition_input) ;
              Transition_output := (* FIXME *) value (option_map Moore.State_output (Moore.getTransition_target m t));
              Transition_dest := t.(Moore.Transition_dest)
            |}  
         
      ]
].

Definition Moore2Mealy := parse Moore2Mealy'.

Close Scope coqtl.

