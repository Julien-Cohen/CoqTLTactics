Require Import String.
Require Import List.

Require Import Moore.
Require Import core.Model.
Require Import core.utils.Utils.

Definition MooreMetamodel_toStates (m: list MooreMetamodel_Object) : list State :=
    optionList2List (map (fun s => (MooreMetamodel_toClass StateClass s)) m).

Definition MooreMetamodel_toTransitions (m: list MooreMetamodel_Object) : list Transition :=
    optionList2List (map (fun s => (MooreMetamodel_toClass TransitionClass s)) m).

Definition MooreMetamodel_allStates (m: MooreModel) : list State :=
    MooreMetamodel_toStates (allModelElements m).

Definition MooreMetamodel_allTransitions (m: MooreModel) : list Transition :=
    MooreMetamodel_toTransitions (allModelElements m).

Definition initialState (m: MooreModel) : option State :=
    find (fun s => eqb "S0" (State_getName s)) (MooreMetamodel_allStates m).


Definition State_outTransitions (s: State) (m: MooreModel) : list Transition :=
    filter (fun t => 
        match (Transition_getSource t m) with
        | Some s' => beq_State s s'
        | None => false
        end)
        (MooreMetamodel_allTransitions m).

Definition State_acceptTransition (s: State) (m: MooreModel) (i: string) : option Transition :=
    find (fun t => eqb i (Transition_getInput t)) (State_outTransitions s m).
        
Fixpoint executeFromState (m: MooreModel) (current: State) (remainingInput: list string) : list string :=
    match remainingInput with 
    | i :: is => 
        let outTransition :=  State_acceptTransition current m i in
        let trgState := 
            match outTransition with 
            | Some t =>  Transition_getTarget t m
            | None => None
            end in
        match trgState with
        | Some s => (State_getOutput s) :: (executeFromState m s is)
        | None => nil
        end
    | _ => nil 
    end.

Definition Moore_execute (m: MooreModel) (input: list string) : list string :=
    match (initialState m) with 
    | Some s => executeFromState m s input
    | None => nil
    end.

Require Import tests.sampleMoore.

Compute Moore_execute InputModel ("1"::"0"::"1"::nil).



