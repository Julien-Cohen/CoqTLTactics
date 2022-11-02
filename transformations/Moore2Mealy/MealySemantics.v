Require Import String.
Require Import List.

Require Import Mealy.
Require Import core.Model.
Require Import core.utils.Utils.

Definition MealyMetamodel_toStates (m: list MealyMetamodel_Object) : list State :=
    optionList2List (map (fun s => (MealyMetamodel_toClass StateClass s)) m).

Definition MealyMetamodel_toTransitions (m: list MealyMetamodel_Object) : list Transition :=
    optionList2List (map (fun s => (MealyMetamodel_toClass TransitionClass s)) m).

Definition MealyMetamodel_allStates (m: MealyModel) : list State :=
    MealyMetamodel_toStates (allModelElements m).

Definition MealyMetamodel_allTransitions (m: MealyModel) : list Transition :=
    MealyMetamodel_toTransitions (allModelElements m).

Definition initialState (m: MealyModel) : option State :=
    find (fun s => eqb "S0" (State_getName s)) (MealyMetamodel_allStates m).

Definition State_outTransitions (s: State) (m: MealyModel) : list Transition :=
    filter (fun t => 
        match (Transition_getSource t m) with
        | Some s' => beq_State s s'
        | None => false
        end)
        (MealyMetamodel_allTransitions m).

Definition State_acceptTransition (s: State) (m: MealyModel) (i: string) : option Transition :=
    find (fun t => eqb i (Transition_getInput t)) (State_outTransitions s m).        

Fixpoint executeFromState (m: MealyModel) (current: State) (remainingInput: list string) : list string :=
    match remainingInput with 
    | i :: is => 
        let outTransition := State_acceptTransition current m i in            
        let trgState := 
            match outTransition with 
            | Some t =>  Transition_getTarget t m
            | None => None
            end in
        match trgState with
        | Some s => 
            match outTransition with 
            | Some t =>  (Transition_getOutput t) :: (executeFromState m s is)
            | None => (executeFromState m s is)
            end
        | None => nil
        end
    | _ => nil 
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



