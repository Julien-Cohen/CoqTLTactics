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

Definition convert_state (s:State_t) : Mealy.State_t :=
  {| Mealy.State_id := s.(State_id) |}.

Definition convert_transition m (t : Transition_t) : option Mealy.Transition_t :=
  s <- getTransition_target m t ;
  return {| 
       Mealy.Transition_id :=  t.(Transition_id) ;
       Mealy.Transition_input := t.(Transition_input) ;
       Mealy.Transition_output := s.(State_output) 
     |}
.


Definition contains (elements: list Moore.Element) element : bool :=
  (existsb (Moore.State_t_beq element) (lift_list (Moore.get_E_data Moore.State_K) elements) ).


  

Definition well_form (m: Moore.M) : bool :=
  (forallb (contains m.(Model.modelElements)) 
           (optionList2List (
              map (fun tr => Moore.getTransition_target m tr)
                  (lift_list (Moore.get_E_data Moore.Transition_K) m.(Model.modelElements))
              )
            )
  ).


Definition Moore2Mealy' :=
    transformation
    [
      rule "state"
      from [State_K]
      to [
        ELEM "s" ::: Mealy.State_K  
           fun _ _ s => return convert_state s 
      ];
      
      rule "transition"
      from [Transition_K]
      where (fun m _ => well_form m)
      to [
        ELEM "t" ::: Mealy.Transition_K
           fun _ m t => convert_transition m t  
          
        LINK ::: Mealy.Transition_source_K 
           fun tls _ m moore_tr mealy_tr =>
             t_source <- Transition_getSourceObject moore_tr m ;
             res <- resolve tls "s" Mealy.State_K (singleton t_source) ;
             do_glue mealy_tr with res 
           ;

        LINK ::: Mealy.Transition_target_K 
           fun tls _ m moore_tr mealy_tr =>
             t_target <- Transition_getTargetObject moore_tr m ;
             res <- resolve tls "s" Mealy.State_K (singleton t_target) ;
             do_glue mealy_tr with res 
          
      ]
].
    
Definition Moore2Mealy := parse Moore2Mealy'.

Close Scope coqtl.

  
