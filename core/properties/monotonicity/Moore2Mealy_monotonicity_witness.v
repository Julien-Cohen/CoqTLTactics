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

Definition Moore2Mealy' :=
    transformation
    [
      rule "state"
      from [Moore.State_K]
      where (fun m s => 
              negb (existsb (Moore.State_t_beq s) 
                       (optionList2List (map 
                          (fun tr => Moore.getTransition_target m tr)
                          (lift_list (Moore.get_E_data Moore.Transition_K) m.(Model.modelElements)))))) (* fixme *)
      to [
        elem [Moore.State_K] Mealy.State_K "s"
          (fun _ _ s => return Build_State_t s.(Moore.State_id)) nil
      ]
].

Definition Moore2Mealy := parse Moore2Mealy'.

Close Scope coqtl.

  
