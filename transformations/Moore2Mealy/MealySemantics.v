Require Import String.
Require Import List.

Require Import Mealy.
Require Import core.Model.
Require Import core.utils.Utils.

Definition MealyMetamodel_toStates (m: list Element) : list State_t :=
    optionList2List (map (fun s => (get_E_data State_K s)) m).

Definition MealyMetamodel_toTransitions (m: list Element) : list Transition_t :=
    optionList2List (map (fun s => (get_E_data Transition_K s)) m).

Definition MealyMetamodel_allStates (m: M) : list State_t :=
    MealyMetamodel_toStates m.(modelElements).

Definition MealyMetamodel_allTransitions (m: M) : list Transition_t :=
    MealyMetamodel_toTransitions m.(modelElements).

Definition initialState (m: M) : option State_t :=
    find (fun s => eqb "S0" s.(State_name)) (MealyMetamodel_allStates m).

Definition State_outTransitions (s: State_t) (m: M) : list Transition_t :=
    filter (fun t => 
        match (getTransition_source t m) with
        | Some s' => State_t_beq s s'
        | None => false
        end)
        (MealyMetamodel_allTransitions m).

Definition State_acceptTransition (s: State_t) (m: M) (i: string) : option Transition_t :=
    find (fun t => eqb i t.(Transition_input)) (State_outTransitions s m).        

Definition search m current i :=
  match State_acceptTransition current m i with
  | None => None
  | Some t => match getTransition_target t m
              with
              | Some s => Some (t, s)
              | None => None (* impossible when models are well formed *)
              end
  end.


Fixpoint executeFromState (m: M) (current: State_t) (remainingInput: list string) : list string :=
  match remainingInput with 
   | i :: inputs => 
       match search m current i with 
        | None => nil
        | Some (t, s) =>    t.(Transition_input) :: (executeFromState m s inputs)

       end
   | nil => nil 
  end.

Definition Mealy_execute (m: M) (input: list string) : list string :=
    match (initialState m) with 
    | Some s => executeFromState m s input
    | None => nil
    end.


Require Import tests.sampleMoore.
Require Import core.Semantics.
Require Import transformations.Moore2Mealy.Moore2Mealy.

Compute Mealy_execute (execute Moore2Mealy InputModel) ("1"::"0"::"1"::nil).



