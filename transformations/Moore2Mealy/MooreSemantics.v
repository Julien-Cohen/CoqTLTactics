Require Import String.
Require Import List.

Require Import Moore.
Require Import core.Model.
Require Import core.utils.Utils.

Definition MooreMetamodel_toStates (m: list Element) : list State_t :=
    optionList2List (map (fun s => get_E_data State_K s) m).

Definition MooreMetamodel_toTransitions (m: list Element) : list Transition_t :=
    optionList2List (map (fun s => get_E_data Transition_K s) m).

Definition MooreMetamodel_allStates (m: Moore.M) : list State_t :=
    MooreMetamodel_toStates m.(modelElements).

Definition MooreMetamodel_allTransitions (m: Moore.M) : list Transition_t :=
    MooreMetamodel_toTransitions m.(modelElements).

Definition initialState (m: Moore.M) : option State_t :=
    find (fun s => eqb "S0" s.(State_name)) (MooreMetamodel_allStates m).


Definition State_outTransitions (s: State_t) (m: Moore.M) : list Transition_t :=
    filter (fun t => 
        match (getTransition_source t m) with
        | Some s' => State_t_beq s s'
        | None => false
        end)
        (MooreMetamodel_allTransitions m).

Definition State_acceptTransition (m: Moore.M) (s: State_t) (i: string) : option Transition_t :=
    find (fun t => eqb i t.(Transition_input)) (State_outTransitions s m).
        
Definition search m current i :=
  let outTransition :=  State_acceptTransition m current i in
  match outTransition with 
    | Some t =>  getTransition_target t m
    | None => None
    end.

Fixpoint executeFromState (m: Moore.M) (current: State_t) (remainingInput: list string) : list string :=
    match remainingInput with 
    | i :: is =>      
        match search m current i with
        | Some s => s.(State_output) :: (executeFromState m s is)
        | None => nil
        end
    | _ => nil 
    end.

Definition Moore_execute (m: Moore.M) (input: list string) : list string :=
    match initialState m with 
    | Some s => executeFromState m s input
    | None => nil
    end.

Require Import tests.sampleMoore.

Compute Moore_execute InputModel ("1"::"0"::"1"::nil).



