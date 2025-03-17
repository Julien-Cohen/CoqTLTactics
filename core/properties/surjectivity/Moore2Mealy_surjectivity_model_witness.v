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
  Build_TransformationConfiguration Moore.MM Mealy.MM.

#[export]  
Instance Moore2MealyModelingTransformationConfiguration : ModelingTransformationConfiguration Moore2MealyTransformationConfiguration :=
 Build_ModelingTransformationConfiguration Moore2MealyTransformationConfiguration Moore.MMM Mealy.MMM.

Open Scope coqtl.

Import Glue.
Import Nat.

Import Moore.

Definition convert_state : Mealy.State_t :=
  {| Mealy.State_id := (Id.Id "S0") |}.

(** a transformation that always generate the same element *)

Definition Moore2Mealy' :=
    transformation
    [     
      rule "state"
      from [State_K]
      to [
        ELEM "s" ::: Mealy.State_K  
           fun _ _ s => return convert_state 
      ];
      
      rule "transition"
      from [Transition_K]
      to [
        ELEM "t" ::: Mealy.State_K
          fun _ _ s => return convert_state 
      ]
].
    
Definition Moore2Mealy := parse Moore2Mealy'.

Close Scope coqtl.

  
