Require Import String.
Require Import List.

Require Import Mealy.
Require Import core.Model.
Require Import core.utils.Utils.

Definition MealyMetamodel_toStates (m: list MealyMetamodel_Object) : list State :=
    optionList2List (map (fun s => (MealyMetamodel_toClass State_K s)) m).

Definition MealyMetamodel_toTransitions (m: list MealyMetamodel_Object) : list Transition :=
    optionList2List (map (fun s => (MealyMetamodel_toClass Transition_K s)) m).

Definition MealyMetamodel_allStates (m: MealyModel) : list State :=
    MealyMetamodel_toStates m.(modelElements).

Definition MealyMetamodel_allTransitions (m: MealyModel) : list Transition :=
    MealyMetamodel_toTransitions m.(modelElements).

Definition initialState (m: MealyModel) : option State :=
    find (fun s => eqb "S0" s.(name)) (MealyMetamodel_allStates m).

Definition State_outTransitions (s: State) (m: MealyModel) : list Transition :=
    filter (fun t => 
        match (Transition_getSource t m) with
        | Some s' => beq_State s s'
        | None => false
        end)
        (MealyMetamodel_allTransitions m).

Definition State_acceptTransition (s: State) (m: MealyModel) (i: string) : option Transition :=
    find (fun t => eqb i t.(input)) (State_outTransitions s m).        

Definition search m current i :=
  match State_acceptTransition current m i with
  | None => None
  | Some t => match Transition_getTarget t m
              with
              | Some s => Some (t, s)
              | None => None (* impossible when models are well formed *)
              end
  end.


Fixpoint executeFromState (m: MealyModel) (current: State) (remainingInput: list string) : list string :=
  match remainingInput with 
   | i :: inputs => 
       match search m current i with 
        | None => nil
        | Some (t, s) =>    t.(input) :: (executeFromState m s inputs)

       end
   | nil => nil 
  end.

Definition Mealy_execute (m: MealyModel) (input: list string) : list string :=
    match (initialState m) with 
    | Some s => executeFromState m s input
    | None => nil
    end.


Require Import tests.sampleMoore.
Require Import core.Semantics.
Require Import transformations.Moore2Mealy.Moore2Mealy.

Compute Mealy_execute (execute Moore2Mealy InputModel) ("1"::"0"::"1"::nil).



