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
Record FStateMachine_t := { FStateMachine_name : string ; FStateMachine_FStateMachineID : string }.
Scheme Equality for FStateMachine_t.
Record FTransition_t := { FTransition_label : string ; FTransition_FTransitionID : string }.
Scheme Equality for FTransition_t.
Record FAbstractState_t := { FAbstractState_name : string ; FAbstractState_FAbstractStateID : string }.
Scheme Equality for FAbstractState_t.
Record FInitialState_t := { FInitialState_FInitialStateID : string }.
Scheme Equality for FInitialState_t.
Record FRegularState_t := { FRegularState_FRegularStateID : string }.
Scheme Equality for FRegularState_t.

(** Base types for links *)
Record FStateMachinetransitions_t := { FStateMachinetransitions_t_source : FStateMachine_t ; FStateMachinetransitions_t_target : list FTransition_t }.
Definition FStateMachinetransitions_t_beq (a1 a2: FStateMachinetransitions_t) : bool := 
  FStateMachine_t_beq a1.(FStateMachinetransitions_t_source) a2.(FStateMachinetransitions_t_source) && list_beq FTransition_t_beq a1.(FStateMachinetransitions_t_target) a2.(FStateMachinetransitions_t_target).
Record FStateMachinestates_t := { FStateMachinestates_t_source : FStateMachine_t ; FStateMachinestates_t_target : list FAbstractState_t }.
Definition FStateMachinestates_t_beq (a1 a2: FStateMachinestates_t) : bool := 
  FStateMachine_t_beq a1.(FStateMachinestates_t_source) a2.(FStateMachinestates_t_source) && list_beq FAbstractState_t_beq a1.(FStateMachinestates_t_target) a2.(FStateMachinestates_t_target).
Record FTransitionstateMachine_t := { FTransitionstateMachine_t_source : FTransition_t ; FTransitionstateMachine_t_target : FStateMachine_t }.
Scheme Equality for FTransitionstateMachine_t.
Record FTransitionsource_t := { FTransitionsource_t_source : FTransition_t ; FTransitionsource_t_target : FAbstractState_t }.
Scheme Equality for FTransitionsource_t.
Record FTransitiontarget_t := { FTransitiontarget_t_source : FTransition_t ; FTransitiontarget_t_target : FAbstractState_t }.
Scheme Equality for FTransitiontarget_t.
Record FAbstractStatestateMachine_t := { FAbstractStatestateMachine_t_source : FAbstractState_t ; FAbstractStatestateMachine_t_target : FStateMachine_t }.
Scheme Equality for FAbstractStatestateMachine_t.

(** Data types for element (to build models) *)
Inductive Element : Set :=
  | FStateMachineElement : FStateMachine_t -> Element
  | FTransitionElement : FTransition_t -> Element
  | FAbstractStateElement : FAbstractState_t -> Element
  | FInitialStateElement : FInitialState_t -> Element
  | FRegularStateElement : FRegularState_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  | FStateMachinetransitionsLink : FStateMachinetransitions_t -> Link
  | FStateMachinestatesLink : FStateMachinestates_t -> Link
  | FTransitionstateMachineLink : FTransitionstateMachine_t -> Link
  | FTransitionsourceLink : FTransitionsource_t -> Link
  | FTransitiontargetLink : FTransitiontarget_t -> Link
  | FAbstractStatestateMachineLink : FAbstractStatestateMachine_t -> Link
.
Definition Link_beq (c1 : Link) (c2 : Link) : bool :=
  match c1, c2 with
  | FStateMachinetransitionsLink o1, FStateMachinetransitionsLink o2 => FStateMachinetransitions_t_beq o1 o2
  | FStateMachinestatesLink o1, FStateMachinestatesLink o2 => FStateMachinestates_t_beq o1 o2
  | FTransitionstateMachineLink o1, FTransitionstateMachineLink o2 => FTransitionstateMachine_t_beq o1 o2
  | FTransitionsourceLink o1, FTransitionsourceLink o2 => FTransitionsource_t_beq o1 o2
  | FTransitiontargetLink o1, FTransitiontargetLink o2 => FTransitiontarget_t_beq o1 o2
  | FAbstractStatestateMachineLink o1, FAbstractStatestateMachineLink o2 => FAbstractStatestateMachine_t_beq o1 o2
  | _, _ => false
  end.

(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
| FStateMachine_K
| FTransition_K
| FAbstractState_K
| FInitialState_K
| FRegularState_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
  | FStateMachinetransitions_K
  | FStateMachinestates_K
  | FTransitionstateMachine_K
  | FTransitionsource_K
  | FTransitiontarget_K
  | FAbstractStatestateMachine_K
.
Scheme Equality for LinkKind.

(** Reflective functions (typing : correspondence between abstract types (kinds) and model data) *)
Definition getTypeByEKind (k : ElementKind) : Set :=
  match k with
  | FStateMachine_K => FStateMachine_t
  | FTransition_K => FTransition_t
  | FAbstractState_K => FAbstractState_t
  | FInitialState_K => FInitialState_t
  | FRegularState_K => FRegularState_t
  end.


Definition lift_EKind k : (getTypeByEKind k) -> Element := 
  match k with
  | FStateMachine_K => FStateMachineElement
  | FTransition_K => FTransitionElement
  | FAbstractState_K => FAbstractStateElement
  | FInitialState_K => FInitialStateElement
  | FRegularState_K => FRegularStateElement
  end.


Definition get_E_data (k : ElementKind) (c : Element) : option (getTypeByEKind k) :=
  match (k,c) as e return (option (getTypeByEKind (fst e))) with
  | (FStateMachine_K, FStateMachineElement v)  => Some v
  | (FTransition_K, FTransitionElement v)  => Some v
  | (FAbstractState_K, FAbstractStateElement v)  => Some v
  | (FInitialState_K, FInitialStateElement v)  => Some v
  | (FRegularState_K, FRegularStateElement v)  => Some v
  | (_ , _) => None
  end.


Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with
  | FStateMachinetransitions_K => FStateMachinetransitions_t
  | FStateMachinestates_K => FStateMachinestates_t
  | FTransitionstateMachine_K => FTransitionstateMachine_t
  | FTransitionsource_K => FTransitionsource_t
  | FTransitiontarget_K => FTransitiontarget_t
  | FAbstractStatestateMachine_K => FAbstractStatestateMachine_t
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | FStateMachinetransitions_K => FStateMachinetransitionsLink
  | FStateMachinestates_K => FStateMachinestatesLink
  | FTransitionstateMachine_K => FTransitionstateMachineLink
  | FTransitionsource_K => FTransitionsourceLink
  | FTransitiontarget_K => FTransitiontargetLink
  | FAbstractStatestateMachine_K => FAbstractStatestateMachineLink
  end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (FStateMachinetransitions_K, FStateMachinetransitionsLink v)  => Some v
  | (FStateMachinestates_K, FStateMachinestatesLink v)  => Some v
  | (FTransitionstateMachine_K, FTransitionstateMachineLink v)  => Some v
  | (FTransitionsource_K, FTransitionsourceLink v)  => Some v
  | (FTransitiontarget_K, FTransitiontargetLink v)  => Some v
  | (FAbstractStatestateMachine_K, FAbstractStatestateMachineLink v)  => Some v
  | (_ , _) => None
  end.

(** Typeclass Instance *)
Definition FSMMM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eqdec := Element_beq ;
  links_eqdec := Link_beq
|}.


#[export]
Instance FSMElementDenotation : Denotation Element ElementKind :=
{
  denoteDatatype := getTypeByEKind ;
  unbox := get_E_data ;
  constructor := lift_EKind ;
}.


#[export]
Instance FSMLinkDenotation : Denotation Link LinkKind :=
{
  denoteDatatype := getTypeByLKind ;
  unbox := get_L_data ;
  constructor := lift_LKind ;
}.


#[export]
Instance FSMMetamodel : ModelingMetamodel FSMMM :=
{
  elements := FSMElementDenotation ;
  links := FSMLinkDenotation ;
}.


Definition FSMModel := Model FSMMM.

(** General functions (used in transformations) *)
Fixpoint getFStateMachinetransitionsOnLinks (f : FStateMachine_t) (l : list Link) : option (list FTransition_t) :=
match l with
  | (FStateMachinetransitionsLink x) :: l1 =>
    if FStateMachine_t_beq x.(FStateMachinetransitions_t_source) f
      then (Some x.(FStateMachinetransitions_t_target))
      else getFStateMachinetransitionsOnLinks f l1
  | _ :: l1 => getFStateMachinetransitionsOnLinks f l1
  | nil => None
end.


Definition getFStateMachinetransitions (f : FStateMachine_t) (m : FSMModel) : option (list FTransition_t) :=
  getFStateMachinetransitionsOnLinks f m.(modelLinks).


Fixpoint getFStateMachinestatesOnLinks (f : FStateMachine_t) (l : list Link) : option (list FAbstractState_t) :=
match l with
  | (FStateMachinestatesLink x) :: l1 =>
    if FStateMachine_t_beq x.(FStateMachinestates_t_source) f
      then (Some x.(FStateMachinestates_t_target))
      else getFStateMachinestatesOnLinks f l1
  | _ :: l1 => getFStateMachinestatesOnLinks f l1
  | nil => None
end.


Definition getFStateMachinestates (f : FStateMachine_t) (m : FSMModel) : option (list FAbstractState_t) :=
  getFStateMachinestatesOnLinks f m.(modelLinks).


Fixpoint getFTransitionstateMachineOnLinks (f : FTransition_t) (l : list Link) : option (FStateMachine_t) :=
match l with
  | (FTransitionstateMachineLink x) :: l1 =>
    if FTransition_t_beq x.(FTransitionstateMachine_t_source) f
      then (Some x.(FTransitionstateMachine_t_target))
      else getFTransitionstateMachineOnLinks f l1
  | _ :: l1 => getFTransitionstateMachineOnLinks f l1
  | nil => None
end.


Definition getFTransitionstateMachine (f : FTransition_t) (m : FSMModel) : option (FStateMachine_t) :=
  getFTransitionstateMachineOnLinks f m.(modelLinks).


Fixpoint getFTransitionsourceOnLinks (f : FTransition_t) (l : list Link) : option (FAbstractState_t) :=
match l with
  | (FTransitionsourceLink x) :: l1 =>
    if FTransition_t_beq x.(FTransitionsource_t_source) f
      then (Some x.(FTransitionsource_t_target))
      else getFTransitionsourceOnLinks f l1
  | _ :: l1 => getFTransitionsourceOnLinks f l1
  | nil => None
end.


Definition getFTransitionsource (f : FTransition_t) (m : FSMModel) : option (FAbstractState_t) :=
  getFTransitionsourceOnLinks f m.(modelLinks).


Fixpoint getFTransitiontargetOnLinks (f : FTransition_t) (l : list Link) : option (FAbstractState_t) :=
match l with
  | (FTransitiontargetLink x) :: l1 =>
    if FTransition_t_beq x.(FTransitiontarget_t_source) f
      then (Some x.(FTransitiontarget_t_target))
      else getFTransitiontargetOnLinks f l1
  | _ :: l1 => getFTransitiontargetOnLinks f l1
  | nil => None
end.


Definition getFTransitiontarget (f : FTransition_t) (m : FSMModel) : option (FAbstractState_t) :=
  getFTransitiontargetOnLinks f m.(modelLinks).


Fixpoint getFAbstractStatestateMachineOnLinks (f : FAbstractState_t) (l : list Link) : option (FStateMachine_t) :=
match l with
  | (FAbstractStatestateMachineLink x) :: l1 =>
    if FAbstractState_t_beq x.(FAbstractStatestateMachine_t_source) f
      then (Some x.(FAbstractStatestateMachine_t_target))
      else getFAbstractStatestateMachineOnLinks f l1
  | _ :: l1 => getFAbstractStatestateMachineOnLinks f l1
  | nil => None
end.


Definition getFAbstractStatestateMachine (f : FAbstractState_t) (m : FSMModel) : option (FStateMachine_t) :=
  getFAbstractStatestateMachineOnLinks f m.(modelLinks).



(** Useful lemmas *)
Lemma FSM_invert : 
  forall (k: ElementKind) (t1 t2: getTypeByEKind k),
    constructor k t1 = constructor k t2 -> t1 = t2.
Proof. Admitted. 


Lemma Element_dec : 
  forall (a: Element),
(instanceof FStateMachine_K a) = true\/(instanceof FTransition_K a) = true\/(instanceof FAbstractState_K a) = true\/(instanceof FInitialState_K a) = true\/(instanceof FRegularState_K a) = true
.
Proof. Admitted. 


Lemma FStateMachineElement_cast :
  forall x y,
    unbox FStateMachine_K x = return y -> FStateMachineElement y = x.
Proof. Admitted. 


Lemma FTransitionElement_cast :
  forall x y,
    unbox FTransition_K x = return y -> FTransitionElement y = x.
Proof. Admitted. 


Lemma FAbstractStateElement_cast :
  forall x y,
    unbox FAbstractState_K x = return y -> FAbstractStateElement y = x.
Proof. Admitted. 


Lemma FInitialStateElement_cast :
  forall x y,
    unbox FInitialState_K x = return y -> FInitialStateElement y = x.
Proof. Admitted. 


Lemma FRegularStateElement_cast :
  forall x y,
    unbox FRegularState_K x = return y -> FRegularStateElement y = x.
Proof. Admitted. 



