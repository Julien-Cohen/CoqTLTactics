(** Moore to Mealy transformation. *)

Require Import String List.


From core 
  Require Import utils.Utils TransformationConfiguration.

From core.modeling 
  Require Import 
  ConcreteSyntax ModelingSemantics ConcreteExpressions Parser ModelingTransformationConfiguration.

From transformations.Moore2Mealy
  Require 
  Moore Mealy.

Import Glue.


#[export]
Instance Moore2MealyTransformationConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration Moore.MM Mealy.MM.

#[export]  
Instance Moore2MealyModelingTransformationConfiguration : ModelingTransformationConfiguration Moore2MealyTransformationConfiguration :=
 Build_ModelingTransformationConfiguration Moore2MealyTransformationConfiguration Moore.MMM Mealy.MMM.

Open Scope coqtl.


Import Moore. (* For readability, we import Moore but not Mealy. *)

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

