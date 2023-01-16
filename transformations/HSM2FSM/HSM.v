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
Record StateMachine_t := { StateMachine_name : string ; StateMachine_StateMachineID : string }.
Scheme Equality for StateMachine_t.
Record Transition_t := { Transition_label : string ; Transition_TransitionID : string }.
Scheme Equality for Transition_t.
Record AbstractState_t := { AbstractState_name : string ; AbstractState_AbstractStateID : string }.
Scheme Equality for AbstractState_t.
Record InitialState_t := { InitialState_InitialStateID : string }.
Scheme Equality for InitialState_t.
Record RegularState_t := { RegularState_RegularStateID : string }.
Scheme Equality for RegularState_t.
Record CompositeState_t := { CompositeState_CompositeStateID : string }.
Scheme Equality for CompositeState_t.

(** Base types for links *)
Record StateMachinetransitions_t := { StateMachinetransitions_t_source : StateMachine_t ; StateMachinetransitions_t_target : list Transition_t }.
Definition StateMachinetransitions_t_beq (a1 a2: StateMachinetransitions_t) : bool := 
  StateMachine_t_beq a1.(StateMachinetransitions_t_source) a2.(StateMachinetransitions_t_source) && list_beq Transition_t_beq a1.(StateMachinetransitions_t_target) a2.(StateMachinetransitions_t_target).
Record StateMachinestates_t := { StateMachinestates_t_source : StateMachine_t ; StateMachinestates_t_target : list AbstractState_t }.
Definition StateMachinestates_t_beq (a1 a2: StateMachinestates_t) : bool := 
  StateMachine_t_beq a1.(StateMachinestates_t_source) a2.(StateMachinestates_t_source) && list_beq AbstractState_t_beq a1.(StateMachinestates_t_target) a2.(StateMachinestates_t_target).
Record TransitionstateMachine_t := { TransitionstateMachine_t_source : Transition_t ; TransitionstateMachine_t_target : StateMachine_t }.
Scheme Equality for TransitionstateMachine_t.
Record Transitionsource_t := { Transitionsource_t_source : Transition_t ; Transitionsource_t_target : AbstractState_t }.
Scheme Equality for Transitionsource_t.
Record Transitiontarget_t := { Transitiontarget_t_source : Transition_t ; Transitiontarget_t_target : AbstractState_t }.
Scheme Equality for Transitiontarget_t.
Record AbstractStatestateMachine_t := { AbstractStatestateMachine_t_source : AbstractState_t ; AbstractStatestateMachine_t_target : StateMachine_t }.
Scheme Equality for AbstractStatestateMachine_t.
Record AbstractStatecompositeState_t := { AbstractStatecompositeState_t_source : AbstractState_t ; AbstractStatecompositeState_t_target : CompositeState_t }.
Scheme Equality for AbstractStatecompositeState_t.
Record CompositeStatestates_t := { CompositeStatestates_t_source : CompositeState_t ; CompositeStatestates_t_target : list AbstractState_t }.
Definition CompositeStatestates_t_beq (a1 a2: CompositeStatestates_t) : bool := 
  CompositeState_t_beq a1.(CompositeStatestates_t_source) a2.(CompositeStatestates_t_source) && list_beq AbstractState_t_beq a1.(CompositeStatestates_t_target) a2.(CompositeStatestates_t_target).

(** Data types for element (to build models) *)
Inductive Element : Set :=
  | StateMachineElement : StateMachine_t -> Element
  | TransitionElement : Transition_t -> Element
  | AbstractStateElement : AbstractState_t -> Element
  | InitialStateElement : InitialState_t -> Element
  | RegularStateElement : RegularState_t -> Element
  | CompositeStateElement : CompositeState_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  | StateMachinetransitionsLink : StateMachinetransitions_t -> Link
  | StateMachinestatesLink : StateMachinestates_t -> Link
  | TransitionstateMachineLink : TransitionstateMachine_t -> Link
  | TransitionsourceLink : Transitionsource_t -> Link
  | TransitiontargetLink : Transitiontarget_t -> Link
  | AbstractStatestateMachineLink : AbstractStatestateMachine_t -> Link
  | AbstractStatecompositeStateLink : AbstractStatecompositeState_t -> Link
  | CompositeStatestatesLink : CompositeStatestates_t -> Link
.
Definition Link_beq (c1 : Link) (c2 : Link) : bool :=
  match c1, c2 with
  | StateMachinetransitionsLink o1, StateMachinetransitionsLink o2 => StateMachinetransitions_t_beq o1 o2
  | StateMachinestatesLink o1, StateMachinestatesLink o2 => StateMachinestates_t_beq o1 o2
  | TransitionstateMachineLink o1, TransitionstateMachineLink o2 => TransitionstateMachine_t_beq o1 o2
  | TransitionsourceLink o1, TransitionsourceLink o2 => Transitionsource_t_beq o1 o2
  | TransitiontargetLink o1, TransitiontargetLink o2 => Transitiontarget_t_beq o1 o2
  | AbstractStatestateMachineLink o1, AbstractStatestateMachineLink o2 => AbstractStatestateMachine_t_beq o1 o2
  | AbstractStatecompositeStateLink o1, AbstractStatecompositeStateLink o2 => AbstractStatecompositeState_t_beq o1 o2
  | CompositeStatestatesLink o1, CompositeStatestatesLink o2 => CompositeStatestates_t_beq o1 o2
  | _, _ => false
  end.

(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
| StateMachine_K
| Transition_K
| AbstractState_K
| InitialState_K
| RegularState_K
| CompositeState_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
  | StateMachinetransitions_K
  | StateMachinestates_K
  | TransitionstateMachine_K
  | Transitionsource_K
  | Transitiontarget_K
  | AbstractStatestateMachine_K
  | AbstractStatecompositeState_K
  | CompositeStatestates_K
.
Scheme Equality for LinkKind.

(** Reflective functions (typing : correspondence between abstract types (kinds) and model data) *)
Definition getTypeByEKind (k : ElementKind) : Set :=
  match k with
  | StateMachine_K => StateMachine_t
  | Transition_K => Transition_t
  | AbstractState_K => AbstractState_t
  | InitialState_K => InitialState_t
  | RegularState_K => RegularState_t
  | CompositeState_K => CompositeState_t
  end.


Definition lift_EKind k : (getTypeByEKind k) -> Element := 
  match k with
  | StateMachine_K => StateMachineElement
  | Transition_K => TransitionElement
  | AbstractState_K => AbstractStateElement
  | InitialState_K => InitialStateElement
  | RegularState_K => RegularStateElement
  | CompositeState_K => CompositeStateElement
  end.


Definition get_E_data (k : ElementKind) (c : Element) : option (getTypeByEKind k) :=
  match (k,c) as e return (option (getTypeByEKind (fst e))) with
  | (StateMachine_K, StateMachineElement v)  => Some v
  | (Transition_K, TransitionElement v)  => Some v
  | (AbstractState_K, AbstractStateElement v)  => Some v
  | (InitialState_K, InitialStateElement v)  => Some v
  | (RegularState_K, RegularStateElement v)  => Some v
  | (CompositeState_K, CompositeStateElement v)  => Some v
  | (_ , _) => None
  end.


Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with
  | StateMachinetransitions_K => StateMachinetransitions_t
  | StateMachinestates_K => StateMachinestates_t
  | TransitionstateMachine_K => TransitionstateMachine_t
  | Transitionsource_K => Transitionsource_t
  | Transitiontarget_K => Transitiontarget_t
  | AbstractStatestateMachine_K => AbstractStatestateMachine_t
  | AbstractStatecompositeState_K => AbstractStatecompositeState_t
  | CompositeStatestates_K => CompositeStatestates_t
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | StateMachinetransitions_K => StateMachinetransitionsLink
  | StateMachinestates_K => StateMachinestatesLink
  | TransitionstateMachine_K => TransitionstateMachineLink
  | Transitionsource_K => TransitionsourceLink
  | Transitiontarget_K => TransitiontargetLink
  | AbstractStatestateMachine_K => AbstractStatestateMachineLink
  | AbstractStatecompositeState_K => AbstractStatecompositeStateLink
  | CompositeStatestates_K => CompositeStatestatesLink
  end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (StateMachinetransitions_K, StateMachinetransitionsLink v)  => Some v
  | (StateMachinestates_K, StateMachinestatesLink v)  => Some v
  | (TransitionstateMachine_K, TransitionstateMachineLink v)  => Some v
  | (Transitionsource_K, TransitionsourceLink v)  => Some v
  | (Transitiontarget_K, TransitiontargetLink v)  => Some v
  | (AbstractStatestateMachine_K, AbstractStatestateMachineLink v)  => Some v
  | (AbstractStatecompositeState_K, AbstractStatecompositeStateLink v)  => Some v
  | (CompositeStatestates_K, CompositeStatestatesLink v)  => Some v
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


Fixpoint getStateMachinestatesOnLinks (s : StateMachine_t) (l : list Link) : option (list AbstractState_t) :=
match l with
  | (StateMachinestatesLink x) :: l1 =>
    if StateMachine_t_beq x.(StateMachinestates_t_source) s
      then (Some x.(StateMachinestates_t_target))
      else getStateMachinestatesOnLinks s l1
  | _ :: l1 => getStateMachinestatesOnLinks s l1
  | nil => None
end.


Definition getStateMachinestates (s : StateMachine_t) (m : HSMModel) : option (list AbstractState_t) :=
  getStateMachinestatesOnLinks s m.(modelLinks).


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


Fixpoint getTransitionsourceOnLinks (t : Transition_t) (l : list Link) : option (AbstractState_t) :=
match l with
  | (TransitionsourceLink x) :: l1 =>
    if Transition_t_beq x.(Transitionsource_t_source) t
      then (Some x.(Transitionsource_t_target))
      else getTransitionsourceOnLinks t l1
  | _ :: l1 => getTransitionsourceOnLinks t l1
  | nil => None
end.


Definition getTransitionsource (t : Transition_t) (m : HSMModel) : option (AbstractState_t) :=
  getTransitionsourceOnLinks t m.(modelLinks).


Fixpoint getTransitiontargetOnLinks (t : Transition_t) (l : list Link) : option (AbstractState_t) :=
match l with
  | (TransitiontargetLink x) :: l1 =>
    if Transition_t_beq x.(Transitiontarget_t_source) t
      then (Some x.(Transitiontarget_t_target))
      else getTransitiontargetOnLinks t l1
  | _ :: l1 => getTransitiontargetOnLinks t l1
  | nil => None
end.


Definition getTransitiontarget (t : Transition_t) (m : HSMModel) : option (AbstractState_t) :=
  getTransitiontargetOnLinks t m.(modelLinks).


Fixpoint getAbstractStatestateMachineOnLinks (a : AbstractState_t) (l : list Link) : option (StateMachine_t) :=
match l with
  | (AbstractStatestateMachineLink x) :: l1 =>
    if AbstractState_t_beq x.(AbstractStatestateMachine_t_source) a
      then (Some x.(AbstractStatestateMachine_t_target))
      else getAbstractStatestateMachineOnLinks a l1
  | _ :: l1 => getAbstractStatestateMachineOnLinks a l1
  | nil => None
end.


Definition getAbstractStatestateMachine (a : AbstractState_t) (m : HSMModel) : option (StateMachine_t) :=
  getAbstractStatestateMachineOnLinks a m.(modelLinks).


Fixpoint getAbstractStatecompositeStateOnLinks (a : AbstractState_t) (l : list Link) : option (CompositeState_t) :=
match l with
  | (AbstractStatecompositeStateLink x) :: l1 =>
    if AbstractState_t_beq x.(AbstractStatecompositeState_t_source) a
      then (Some x.(AbstractStatecompositeState_t_target))
      else getAbstractStatecompositeStateOnLinks a l1
  | _ :: l1 => getAbstractStatecompositeStateOnLinks a l1
  | nil => None
end.


Definition getAbstractStatecompositeState (a : AbstractState_t) (m : HSMModel) : option (CompositeState_t) :=
  getAbstractStatecompositeStateOnLinks a m.(modelLinks).


Fixpoint getCompositeStatestatesOnLinks (c : CompositeState_t) (l : list Link) : option (list AbstractState_t) :=
match l with
  | (CompositeStatestatesLink x) :: l1 =>
    if CompositeState_t_beq x.(CompositeStatestates_t_source) c
      then (Some x.(CompositeStatestates_t_target))
      else getCompositeStatestatesOnLinks c l1
  | _ :: l1 => getCompositeStatestatesOnLinks c l1
  | nil => None
end.


Definition getCompositeStatestates (c : CompositeState_t) (m : HSMModel) : option (list AbstractState_t) :=
  getCompositeStatestatesOnLinks c m.(modelLinks).



(** Useful lemmas *)
Lemma HSM_invert : 
  forall (k: ElementKind) (t1 t2: getTypeByEKind k),
    constructor k t1 = constructor k t2 -> t1 = t2.
Proof. Admitted. 


Lemma Element_dec : 
  forall (a: Element),
(instanceof StateMachine_K a) = true\/(instanceof Transition_K a) = true\/(instanceof AbstractState_K a) = true\/(instanceof InitialState_K a) = true\/(instanceof RegularState_K a) = true\/(instanceof CompositeState_K a) = true
.
Proof. Admitted. 


Lemma StateMachineElement_cast :
  forall x y,
    unbox StateMachine_K x = return y -> StateMachineElement y = x.
Proof. Admitted. 


Lemma TransitionElement_cast :
  forall x y,
    unbox Transition_K x = return y -> TransitionElement y = x.
Proof. Admitted. 


Lemma AbstractStateElement_cast :
  forall x y,
    unbox AbstractState_K x = return y -> AbstractStateElement y = x.
Proof. Admitted. 


Lemma InitialStateElement_cast :
  forall x y,
    unbox InitialState_K x = return y -> InitialStateElement y = x.
Proof. Admitted. 


Lemma RegularStateElement_cast :
  forall x y,
    unbox RegularState_K x = return y -> RegularStateElement y = x.
Proof. Admitted. 


Lemma CompositeStateElement_cast :
  forall x y,
    unbox CompositeState_K x = return y -> CompositeStateElement y = x.
Proof. Admitted. 



