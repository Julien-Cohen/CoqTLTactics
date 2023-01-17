(** Imports Native *)
Require Import String.
Require Import Bool.
Require Import List.
Require Import PeanoNat.
Require Import EqNat.
Require Import Coq.Logic.Eqdep_dec.

(** Imports CoqTL *)
Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.utils.CpdtTactics.
Require        core.Tactics.

(** Base types for elements *)
Record StateMachine_t := { StateMachine_name : string }.
Scheme Equality for StateMachine_t.
Record State_t := { State_name : string ; State_initial : bool }.
Scheme Equality for State_t.
Record Transition_t := { Transition_label : string }.
Scheme Equality for Transition_t.

(** Base types for links *)
Record StateMachinestates_t := { StateMachinestates_t_source : StateMachine_t ; StateMachinestates_t_target : list State_t }.
Definition StateMachinestates_t_beq (a1 a2: StateMachinestates_t) : bool := 
  StateMachine_t_beq a1.(StateMachinestates_t_source) a2.(StateMachinestates_t_source) && list_beq State_t_beq a1.(StateMachinestates_t_target) a2.(StateMachinestates_t_target).
Record StateMachinetransitions_t := { StateMachinetransitions_t_source : StateMachine_t ; StateMachinetransitions_t_target : list Transition_t }.
Definition StateMachinetransitions_t_beq (a1 a2: StateMachinetransitions_t) : bool := 
  StateMachine_t_beq a1.(StateMachinetransitions_t_source) a2.(StateMachinetransitions_t_source) && list_beq Transition_t_beq a1.(StateMachinetransitions_t_target) a2.(StateMachinetransitions_t_target).
Record StatesubStates_t := { StatesubStates_t_source : State_t ; StatesubStates_t_target : list State_t }.
Definition StatesubStates_t_beq (a1 a2: StatesubStates_t) : bool := 
  State_t_beq a1.(StatesubStates_t_source) a2.(StatesubStates_t_source) && list_beq State_t_beq a1.(StatesubStates_t_target) a2.(StatesubStates_t_target).
Record StatestateMachine_t := { StatestateMachine_t_source : State_t ; StatestateMachine_t_target : StateMachine_t }.
Scheme Equality for StatestateMachine_t.
Record Transitionsource_t := { Transitionsource_t_source : Transition_t ; Transitionsource_t_target : State_t }.
Scheme Equality for Transitionsource_t.
Record Transitiontarget_t := { Transitiontarget_t_source : Transition_t ; Transitiontarget_t_target : State_t }.
Scheme Equality for Transitiontarget_t.
Record TransitionstateMachine_t := { TransitionstateMachine_t_source : Transition_t ; TransitionstateMachine_t_target : StateMachine_t }.
Scheme Equality for TransitionstateMachine_t.

(** Data types for element (to build models) *)
Inductive Element : Set :=
  | StateMachineElement : StateMachine_t -> Element
  | StateElement : State_t -> Element
  | TransitionElement : Transition_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  | StateMachinestatesLink : StateMachinestates_t -> Link
  | StateMachinetransitionsLink : StateMachinetransitions_t -> Link
  | StatesubStatesLink : StatesubStates_t -> Link
  | StatestateMachineLink : StatestateMachine_t -> Link
  | TransitionsourceLink : Transitionsource_t -> Link
  | TransitiontargetLink : Transitiontarget_t -> Link
  | TransitionstateMachineLink : TransitionstateMachine_t -> Link
.
Definition Link_beq (c1 : Link) (c2 : Link) : bool :=
  match c1, c2 with
  | StateMachinestatesLink o1, StateMachinestatesLink o2 => StateMachinestates_t_beq o1 o2
  | StateMachinetransitionsLink o1, StateMachinetransitionsLink o2 => StateMachinetransitions_t_beq o1 o2
  | StatesubStatesLink o1, StatesubStatesLink o2 => StatesubStates_t_beq o1 o2
  | StatestateMachineLink o1, StatestateMachineLink o2 => StatestateMachine_t_beq o1 o2
  | TransitionsourceLink o1, TransitionsourceLink o2 => Transitionsource_t_beq o1 o2
  | TransitiontargetLink o1, TransitiontargetLink o2 => Transitiontarget_t_beq o1 o2
  | TransitionstateMachineLink o1, TransitionstateMachineLink o2 => TransitionstateMachine_t_beq o1 o2
  | _, _ => false
  end.

(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
| StateMachine_K
| State_K
| Transition_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
  | StateMachinestates_K
  | StateMachinetransitions_K
  | StatesubStates_K
  | StatestateMachine_K
  | Transitionsource_K
  | Transitiontarget_K
  | TransitionstateMachine_K
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
  | StateMachinestates_K => StateMachinestates_t
  | StateMachinetransitions_K => StateMachinetransitions_t
  | StatesubStates_K => StatesubStates_t
  | StatestateMachine_K => StatestateMachine_t
  | Transitionsource_K => Transitionsource_t
  | Transitiontarget_K => Transitiontarget_t
  | TransitionstateMachine_K => TransitionstateMachine_t
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | StateMachinestates_K => StateMachinestatesLink
  | StateMachinetransitions_K => StateMachinetransitionsLink
  | StatesubStates_K => StatesubStatesLink
  | StatestateMachine_K => StatestateMachineLink
  | Transitionsource_K => TransitionsourceLink
  | Transitiontarget_K => TransitiontargetLink
  | TransitionstateMachine_K => TransitionstateMachineLink
  end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (StateMachinestates_K, StateMachinestatesLink v)  => Some v
  | (StateMachinetransitions_K, StateMachinetransitionsLink v)  => Some v
  | (StatesubStates_K, StatesubStatesLink v)  => Some v
  | (StatestateMachine_K, StatestateMachineLink v)  => Some v
  | (Transitionsource_K, TransitionsourceLink v)  => Some v
  | (Transitiontarget_K, TransitiontargetLink v)  => Some v
  | (TransitionstateMachine_K, TransitionstateMachineLink v)  => Some v
  | (_ , _) => None
  end.

(** Typeclass Instance *)
Definition HSMMM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eqdec := Element_beq ;
  links_eqdec := Link_beq
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
Instance HSMMetamodel : ModelingMetamodel HSMMM :=
{
  elements := HSMElementDenotation ;
  links := HSMLinkDenotation ;
}.


Definition HSMModel := Model HSMMM.

(** General functions (used in transformations) *)
Fixpoint getStateMachinestatesOnLinks (s : StateMachine_t) (l : list Link) : option (list State_t) :=
match l with
  | (StateMachinestatesLink x) :: l1 =>
    if StateMachine_t_beq x.(StateMachinestates_t_source) s
      then (Some x.(StateMachinestates_t_target))
      else getStateMachinestatesOnLinks s l1
  | _ :: l1 => getStateMachinestatesOnLinks s l1
  | nil => None
end.


Definition getStateMachinestates (s : StateMachine_t) (m : HSMModel) : option (list State_t) :=
  getStateMachinestatesOnLinks s m.(modelLinks).


Fixpoint getStateMachinetransitionsOnLinks (s : StateMachine_t) (l : list Link) : option (list Transition_t) :=
match l with
  | (StateMachinetransitionsLink x) :: l1 =>
    if StateMachine_t_beq x.(StateMachinetransitions_t_source) s
      then (Some x.(StateMachinetransitions_t_target))
      else getStateMachinetransitionsOnLinks s l1
  | _ :: l1 => getStateMachinetransitionsOnLinks s l1
  | nil => None
end.


Definition getStateMachinetransitions (s : StateMachine_t) (m : HSMModel) : option (list Transition_t) :=
  getStateMachinetransitionsOnLinks s m.(modelLinks).


Fixpoint getStatesubStatesOnLinks (s : State_t) (l : list Link) : option (list State_t) :=
match l with
  | (StatesubStatesLink x) :: l1 =>
    if State_t_beq x.(StatesubStates_t_source) s
      then (Some x.(StatesubStates_t_target))
      else getStatesubStatesOnLinks s l1
  | _ :: l1 => getStatesubStatesOnLinks s l1
  | nil => None
end.


Definition getStatesubStates (s : State_t) (m : HSMModel) : option (list State_t) :=
  getStatesubStatesOnLinks s m.(modelLinks).


Fixpoint getStatestateMachineOnLinks (s : State_t) (l : list Link) : option (StateMachine_t) :=
match l with
  | (StatestateMachineLink x) :: l1 =>
    if State_t_beq x.(StatestateMachine_t_source) s
      then (Some x.(StatestateMachine_t_target))
      else getStatestateMachineOnLinks s l1
  | _ :: l1 => getStatestateMachineOnLinks s l1
  | nil => None
end.


Definition getStatestateMachine (s : State_t) (m : HSMModel) : option (StateMachine_t) :=
  getStatestateMachineOnLinks s m.(modelLinks).


Fixpoint getTransitionsourceOnLinks (t : Transition_t) (l : list Link) : option (State_t) :=
match l with
  | (TransitionsourceLink x) :: l1 =>
    if Transition_t_beq x.(Transitionsource_t_source) t
      then (Some x.(Transitionsource_t_target))
      else getTransitionsourceOnLinks t l1
  | _ :: l1 => getTransitionsourceOnLinks t l1
  | nil => None
end.


Definition getTransitionsource (t : Transition_t) (m : HSMModel) : option (State_t) :=
  getTransitionsourceOnLinks t m.(modelLinks).


Fixpoint getTransitiontargetOnLinks (t : Transition_t) (l : list Link) : option (State_t) :=
match l with
  | (TransitiontargetLink x) :: l1 =>
    if Transition_t_beq x.(Transitiontarget_t_source) t
      then (Some x.(Transitiontarget_t_target))
      else getTransitiontargetOnLinks t l1
  | _ :: l1 => getTransitiontargetOnLinks t l1
  | nil => None
end.


Definition getTransitiontarget (t : Transition_t) (m : HSMModel) : option (State_t) :=
  getTransitiontargetOnLinks t m.(modelLinks).


Fixpoint getTransitionstateMachineOnLinks (t : Transition_t) (l : list Link) : option (StateMachine_t) :=
match l with
  | (TransitionstateMachineLink x) :: l1 =>
    if Transition_t_beq x.(TransitionstateMachine_t_source) t
      then (Some x.(TransitionstateMachine_t_target))
      else getTransitionstateMachineOnLinks t l1
  | _ :: l1 => getTransitionstateMachineOnLinks t l1
  | nil => None
end.


Definition getTransitionstateMachine (t : Transition_t) (m : HSMModel) : option (StateMachine_t) :=
  getTransitionstateMachineOnLinks t m.(modelLinks).



(** Useful lemmas *)
Lemma HSM_invert : 
  forall (k: ElementKind) (t1 t2: getTypeByEKind k),
    constructor k t1 = constructor k t2 -> t1 = t2.
Proof. Admitted. 


Lemma Element_dec : 
  forall (a: Element),
(instanceof StateMachine_K a) = true\/(instanceof State_K a) = true\/(instanceof Transition_K a) = true
.
Proof. Admitted. 


Lemma StateMachineElement_cast :
  forall x y,
    unbox StateMachine_K x = return y -> StateMachineElement y = x.
Proof. Admitted. 


Lemma StateElement_cast :
  forall x y,
    unbox State_K x = return y -> StateElement y = x.
Proof. Admitted. 


Lemma TransitionElement_cast :
  forall x y,
    unbox Transition_K x = return y -> TransitionElement y = x.
Proof. Admitted. 



