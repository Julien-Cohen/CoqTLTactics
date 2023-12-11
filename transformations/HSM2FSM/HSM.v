(* Automatically generated by Ecore2Coq transformation. *)

(** Imports Native *)
Require Import String.
Require Import Bool.
Require Import List.
Require Import PeanoNat.
Require Import EqNat.

(** Imports CoqTL *)
Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import Glue.

(** Base types for elements *)
Record StateMachine_t := { StateMachine_name : string }.
Scheme Equality for StateMachine_t.


Record State_t := { State_name : string ; State_initial : bool }.
Scheme Equality for State_t.


Record Transition_t := { Transition_label : string }.
Scheme Equality for Transition_t.



(** Base types for links *)
Notation StateMachine_states_glue := (Glue StateMachine_t (list State_t)).


Notation StateMachine_transitions_glue := (Glue StateMachine_t (list Transition_t)).


Notation State_subStates_glue := (Glue State_t (list State_t)).


Notation State_stateMachine_glue := (Glue State_t (StateMachine_t)).


Notation Transition_source_glue := (Glue Transition_t (State_t)).


Notation Transition_target_glue := (Glue Transition_t (State_t)).


Notation Transition_stateMachine_glue := (Glue Transition_t (StateMachine_t)).



(** Data types for element (to build models) *)
Inductive Element : Set :=
  | StateMachineElement : StateMachine_t -> Element
  | StateElement : State_t -> Element
  | TransitionElement : Transition_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  | StateMachine_statesLink : StateMachine_states_glue -> Link
  | StateMachine_transitionsLink : StateMachine_transitions_glue -> Link
  | State_subStatesLink : State_subStates_glue -> Link
  | State_stateMachineLink : State_stateMachine_glue -> Link
  | Transition_sourceLink : Transition_source_glue -> Link
  | Transition_targetLink : Transition_target_glue -> Link
  | Transition_stateMachineLink : Transition_stateMachine_glue -> Link
.

(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
  | StateMachine_K
  | State_K
  | Transition_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
  | StateMachine_states_K
  | StateMachine_transitions_K
  | State_subStates_K
  | State_stateMachine_K
  | Transition_source_K
  | Transition_target_K
  | Transition_stateMachine_K
.
Scheme Equality for LinkKind.

(** Reflective functions (typing : correspondence between abstract types (kinds) and model data) *)
Definition getTypeByEKind (k : ElementKind) : Set :=
  match k with
  | StateMachine_K => StateMachine_t
  | State_K => State_t
  | Transition_K => Transition_t
  end.


Definition lift_EKind k : (getTypeByEKind k) -> Element := 
  match k with
  | StateMachine_K => StateMachineElement
  | State_K => StateElement
  | Transition_K => TransitionElement
  end.


Definition get_E_data (k : ElementKind) (c : Element) : option (getTypeByEKind k) :=
  match (k,c) as e return (option (getTypeByEKind (fst e))) with
  | (StateMachine_K, StateMachineElement v)  => Some v
  | (State_K, StateElement v)  => Some v
  | (Transition_K, TransitionElement v)  => Some v
  | (_ , _) => None
  end.


Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with
  | StateMachine_states_K => StateMachine_states_glue
  | StateMachine_transitions_K => StateMachine_transitions_glue
  | State_subStates_K => State_subStates_glue
  | State_stateMachine_K => State_stateMachine_glue
  | Transition_source_K => Transition_source_glue
  | Transition_target_K => Transition_target_glue
  | Transition_stateMachine_K => Transition_stateMachine_glue
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | StateMachine_states_K => StateMachine_statesLink
  | StateMachine_transitions_K => StateMachine_transitionsLink
  | State_subStates_K => State_subStatesLink
  | State_stateMachine_K => State_stateMachineLink
  | Transition_source_K => Transition_sourceLink
  | Transition_target_K => Transition_targetLink
  | Transition_stateMachine_K => Transition_stateMachineLink
  end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (StateMachine_states_K, StateMachine_statesLink v)  => Some v
  | (StateMachine_transitions_K, StateMachine_transitionsLink v)  => Some v
  | (State_subStates_K, State_subStatesLink v)  => Some v
  | (State_stateMachine_K, State_stateMachineLink v)  => Some v
  | (Transition_source_K, Transition_sourceLink v)  => Some v
  | (Transition_target_K, Transition_targetLink v)  => Some v
  | (Transition_stateMachine_K, Transition_stateMachineLink v)  => Some v
  | (_ , _) => None
  end.

(** Typeclass Instance *)
Definition MM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eq_dec := Element_eq_dec ;
|}.


#[export]
Instance HSMElementDenotation : Denotation Element ElementKind :=
{
  denoteDatatype := getTypeByEKind ;
  unbox := get_E_data ;
  constructor := lift_EKind ;
}.


#[export]
Instance HSMLinkDenotation : Denotation Link LinkKind :=
{
  denoteDatatype := getTypeByLKind ;
  unbox := get_L_data ;
  constructor := lift_LKind ;
}.


#[export]
Instance MMM : ModelingMetamodel MM :=
{
  elements := HSMElementDenotation ;
  links := HSMLinkDenotation ;
}.


Definition M := Model MM.

(** General functions (used in transformations) *)
Fixpoint getStateMachine_statesOnLinks (s : StateMachine_t) (l : list Link) : option (list State_t) :=
 match l with
  | (StateMachine_statesLink x) :: l1 =>
    if StateMachine_t_beq x.(src) s
      then (Some x.(trg))
      else getStateMachine_statesOnLinks s l1
  | _ :: l1 => getStateMachine_statesOnLinks s l1
  | nil => None
 end.


Definition getStateMachine_states (m : M) (s : StateMachine_t) : option (list State_t) :=
  getStateMachine_statesOnLinks s m.(modelLinks).


Fixpoint getStateMachine_transitionsOnLinks (s : StateMachine_t) (l : list Link) : option (list Transition_t) :=
 match l with
  | (StateMachine_transitionsLink x) :: l1 =>
    if StateMachine_t_beq x.(src) s
      then (Some x.(trg))
      else getStateMachine_transitionsOnLinks s l1
  | _ :: l1 => getStateMachine_transitionsOnLinks s l1
  | nil => None
 end.


Definition getStateMachine_transitions (m : M) (s : StateMachine_t) : option (list Transition_t) :=
  getStateMachine_transitionsOnLinks s m.(modelLinks).


Fixpoint getState_subStatesOnLinks (s : State_t) (l : list Link) : option (list State_t) :=
 match l with
  | (State_subStatesLink x) :: l1 =>
    if State_t_beq x.(src) s
      then (Some x.(trg))
      else getState_subStatesOnLinks s l1
  | _ :: l1 => getState_subStatesOnLinks s l1
  | nil => None
 end.


Definition getState_subStates (m : M) (s : State_t) : option (list State_t) :=
  getState_subStatesOnLinks s m.(modelLinks).


Fixpoint getState_stateMachineOnLinks (s : State_t) (l : list Link) : option (StateMachine_t) :=
 match l with
  | (State_stateMachineLink x) :: l1 =>
    if State_t_beq x.(src) s
      then (Some x.(trg))
      else getState_stateMachineOnLinks s l1
  | _ :: l1 => getState_stateMachineOnLinks s l1
  | nil => None
 end.


Definition getState_stateMachine (m : M) (s : State_t) : option (StateMachine_t) :=
  getState_stateMachineOnLinks s m.(modelLinks).


Fixpoint getTransition_sourceOnLinks (t : Transition_t) (l : list Link) : option (State_t) :=
 match l with
  | (Transition_sourceLink x) :: l1 =>
    if Transition_t_beq x.(src) t
      then (Some x.(trg))
      else getTransition_sourceOnLinks t l1
  | _ :: l1 => getTransition_sourceOnLinks t l1
  | nil => None
 end.


Definition getTransition_source (m : M) (t : Transition_t) : option (State_t) :=
  getTransition_sourceOnLinks t m.(modelLinks).


Fixpoint getTransition_targetOnLinks (t : Transition_t) (l : list Link) : option (State_t) :=
 match l with
  | (Transition_targetLink x) :: l1 =>
    if Transition_t_beq x.(src) t
      then (Some x.(trg))
      else getTransition_targetOnLinks t l1
  | _ :: l1 => getTransition_targetOnLinks t l1
  | nil => None
 end.


Definition getTransition_target (m : M) (t : Transition_t) : option (State_t) :=
  getTransition_targetOnLinks t m.(modelLinks).


Fixpoint getTransition_stateMachineOnLinks (t : Transition_t) (l : list Link) : option (StateMachine_t) :=
 match l with
  | (Transition_stateMachineLink x) :: l1 =>
    if Transition_t_beq x.(src) t
      then (Some x.(trg))
      else getTransition_stateMachineOnLinks t l1
  | _ :: l1 => getTransition_stateMachineOnLinks t l1
  | nil => None
 end.


Definition getTransition_stateMachine (m : M) (t : Transition_t) : option (StateMachine_t) :=
  getTransition_stateMachineOnLinks t m.(modelLinks).



