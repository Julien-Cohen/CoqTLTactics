From Stdlib Require Import String List.

From core 
  Require Import utils.Utils TransformationConfiguration Syntax Model Semantics.

From core.modeling 
  Require Import 
  ConcreteSyntax ModelingSemantics ConcreteExpressions Parser ModelingTransformationConfiguration.

From transformations.Moore2Mealy
  Require 
  Moore Mealy.

Import Id Glue.

Open Scope coqtl.


(** Definition of the Confluence *) 


Definition Transformation_permutation  {tc:TransformationConfiguration} (t1 t2: Transformation) := 
  t1.(arity) = t2.(arity) /\ 
  ListUtils.set_eq t1.(rules) t2.(rules).

Definition Confluence {tc:TransformationConfiguration} :=
  forall (t1 t2: Transformation) (sm: SourceModel),
    Transformation_permutation t1 t2 -> Model_equiv (execute t1 sm) (execute t2 sm).


(** Confluence of CoqTL : we build a counter example. *)

#[export]
Instance Moore2MealyTransformationConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration Moore.MM Mealy.MM.

#[export]  
Instance Moore2MealyModelingTransformationConfiguration : ModelingTransformationConfiguration Moore2MealyTransformationConfiguration :=
 Build_ModelingTransformationConfiguration Moore2MealyTransformationConfiguration Moore.MMM Mealy.MMM.

Import Moore. (* For readability, we import Moore but not Mealy. *)

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
           fun _ _ s => return {| Mealy.State_id := s.(State_id) |} 
      ];

      rule "state0"
      from [State_K]
      to [
        ELEM "s" ::: Mealy.State_K  
           fun _ _ s => return {| Mealy.State_id := Id "S0" |}
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
      ]
].

Definition Moore2Mealy'' :=
    transformation
    [
      rule "state0"
      from [State_K]
      to [
        ELEM "s" ::: Mealy.State_K  
           fun _ _ s => return {| Mealy.State_id := Id "S0" |}
      ];

      rule "state"
      from [State_K]
      to [
        ELEM "s" ::: Mealy.State_K  
           fun _ _ s => return {| Mealy.State_id := s.(State_id) |} 
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
      ]
].

Definition Moore_m1 : Model Moore.MM :=
    (Build_Model Moore.MM
        (
            (Transition (Build_Transition_t 0 "0000")) :: 
            (State (Build_State_t  (Id.Id "S0000") "1111")) :: 
            (State (Build_State_t  (Id.Id "S1111") "0000")) ::  
            nil
        )
        (
            (TransitionSource (Build_Glue _ _ (Build_Transition_t 0 "0000") (Build_State_t  (Id.Id "S1111") "0000"))) ::
            (TransitionTarget (Build_Glue _ _ (Build_Transition_t 0 "0000") (Build_State_t  (Id.Id "S0000") "1111"))) ::
            nil
        )
).


Theorem notConfluence : 
  ~ Confluence.
Proof.
  intro.
  specialize (H (parse Moore2Mealy') (parse Moore2Mealy'') Moore_m1).
  assert (Transformation_permutation (parse Moore2Mealy') (parse Moore2Mealy'')). {
    unfold parse,Transformation_permutation,set_eq. crush.
  }
  apply H in H0.
  unfold execute, applyTrLkOnModel in H0.
  simpl in H0.
  unfold Model_equiv in H0. destruct H0. clear H0.
  unfold Model_incl in H1. destruct H1. clear H0.
  simpl in H1.
  specialize (H1 (Mealy.TransitionSource (glue {|
    Mealy.Transition_id := 0;
    Mealy.Transition_input := "0000";
    Mealy.Transition_output := "1111"
    |} with {| Mealy.State_id := Id "S0" |}))). 
  crush.
Qed.

Close Scope coqtl.

