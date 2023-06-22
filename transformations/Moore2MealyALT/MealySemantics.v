Require Import String.
Require Import List.

Require Import transformations.Moore2MealyALT.Mealy.
Require Import core.Model.
Require Import core.utils.Utils.


Definition initialState (m: M) : option State_t :=
    find_lift (get_E_data State_K) (fun s => eqb "S0" s.(State_name)) m.(modelElements).

Definition State_outTransitions (m: M) (s: State_t) : list Transition_t :=
    filter_lift 
      (get_E_data Transition_K) 
      (fun t => 
         match (getTransition_source m t) with
         | Some s' => State_t_beq s s'
         | None => false
         end)
      m.(Model.modelElements).

Definition State_acceptTransition (m: M) (s: State_t) (i: string) : option Transition_t :=
    find (fun t => eqb i t.(Transition_input)) (State_outTransitions m s).

Definition search (m: M) (current: State_t) i :=
  match State_acceptTransition m current i with
  | None => None
  | Some t => match getTransition_target m t
              with
              | Some s => Some (t, s)
              | None => None (* impossible when models are well formed *)
              end
  end.

Fixpoint executeFromState (m: M) (current: State_t) (remainingInput: list string) : option (list string) :=
  match remainingInput with 
   | i :: inputs => 
       match search m current i with
        | None => None 
        | Some (t, s) =>  
            match executeFromState m s inputs with
            | Some r => Some (t.(Transition_input) :: r)
            | None => None
            end
       end
   | nil => Some nil 
  end.

Definition execute (m: M) (input: list string) : option (list string) :=
    match initialState m with 
    | Some s => executeFromState m s input
    | None => None
    end.

Require Import transformations.Moore2MealyALT.tests.sampleMoore.
Require        core.Semantics.
Require Import transformations.Moore2MealyALT.Moore2Mealy.

Compute execute (Semantics.execute Moore2Mealy InputModel) ("1"::"0"::"1"::nil).



