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


Require Import Moore2MealyALT.Id.

(** Base types for elements *)
Record State_t := { State_id : NodeId ; State_output : string }.
Scheme Equality for State_t.

Record Transition_t := { Transition_source : NodeId ; Transition_input : string ; Transition_dest : NodeId }.
Scheme Equality for Transition_t.



(** Base types for links *)
(* No Links *)


(** Data types for element (to build models) *)
Inductive Element : Set :=
  | StateElement : State_t -> Element
  | TransitionElement : Transition_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  . (* Empty type *)


(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
  | State_K
  | Transition_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
  . (* Empty type *)

Scheme Equality for LinkKind.

(** Reflective functions (typing : correspondence between abstract types (kinds) and model data) *)
Definition getTypeByEKind (k : ElementKind) : Set :=
  match k with
  | State_K => State_t
  | Transition_K => Transition_t
  end.


Definition lift_EKind k : (getTypeByEKind k) -> Element := 
  match k with
  | State_K => StateElement
  | Transition_K => TransitionElement
  end.


Definition get_E_data (k : ElementKind) (c : Element) : option (getTypeByEKind k) :=
  match (k,c) as e return (option (getTypeByEKind (fst e))) with
  | (State_K, StateElement v)  => Some v
  | (Transition_K, TransitionElement v)  => Some v
  | (_ , _) => None
  end.


Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  None.

(** Typeclass Instance *)
Definition MM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eq_dec := Element_eq_dec ;
|}.


#[export]
Instance MooreElementDenotation : Denotation Element ElementKind :=
{
  denoteDatatype := getTypeByEKind ;
  unbox := get_E_data ;
  constructor := lift_EKind ;
}.


#[export]
Instance MooreLinkDenotation : Denotation Link LinkKind :=
{
  denoteDatatype := getTypeByLKind ;
  unbox := get_L_data ;
  constructor := lift_LKind ;
}.


#[export]
Instance MMM : ModelingMetamodel MM :=
{
  elements := MooreElementDenotation ;
  links := MooreLinkDenotation ;
}.


Definition M := Model MM.

(** General functions (used in transformations) *)
(* FIXME : generate-me*)
Notation find_State := (find_lift (get_E_data State_K)).

Definition getTransition_source (m : M) (t : Transition_t) : option (State_t) :=
  find_State (fun s => NodeId_beq t.(Transition_source) s.(State_id)) m.(modelElements).  


Definition getTransition_target (m : M) (t : Transition_t) : option (State_t) :=
  find_State (fun s => NodeId_beq t.(Transition_dest) s.(State_id)) m.(modelElements).  

(* FIXME : generate-me*)
Definition WF_target (m:M) : Prop :=
  forall t, 
    List.In (TransitionElement t) m.(modelElements) ->
    SUCCESS ( getTransition_target m t ).

(* FIXME : generate-me*)
Definition WF_source (m:M) :Prop :=
  forall t, 
    List.In (TransitionElement t) m.(modelElements) ->
    SUCCESS ( getTransition_source m t ).

(** Manual addition *)

Lemma In_state : forall (m:Moore.M) e,
         List.In (StateElement e) (Model.modelElements m) <-> List.In e
    (OptionListUtils.lift_list (get_E_data State_K)
       (Model.modelElements m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (StateElement e). auto.
  }  
  {
    apply OptionListUtils.In_lift in H.
    destruct H as (e2 & (G & IN2)).
    destruct e2 ; [ PropUtils.inj G| discriminate G]. 
    assumption.
  }
Qed.


Lemma In_transition : forall (m:Moore.M) e,
         List.In (TransitionElement e) (Model.modelElements m) <-> List.In e
    (OptionListUtils.lift_list (get_E_data Transition_K)
       (Model.modelElements m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (TransitionElement e). auto.
  }  
  {
    apply OptionListUtils.In_lift in H.
    destruct H as (e2 & (G & IN2)).
    destruct e2 ; [ discriminate G | PropUtils.inj G]. 
    assumption.
  }
Qed.


Lemma getTransition_source_inv m t s : 
  getTransition_source m t = Some s ->
  List.In (StateElement s) (Model.modelElements m) /\ Transition_source t = State_id s.
Proof.
  intro H.
  unfold getTransition_source in H.
  apply OptionListUtils.find_lift_some in H.
  destruct H as (? & ? & ? & ?).
  destruct x ; [ PropUtils.inj H | discriminate H].
  apply Id.internal_NodeId_dec_bl in H1.
  auto.
Qed.

Lemma getTransition_target_inv m t s : 
  getTransition_target m t = Some s ->
  List.In (StateElement s) (Model.modelElements m) /\ Transition_dest t = State_id s.
Proof.
  intro H.
  unfold getTransition_target in H.
  apply OptionListUtils.find_lift_some in H.
  destruct H as (? & ? & ? & ?).
  destruct x ; [ PropUtils.inj H | discriminate H].
  apply Id.internal_NodeId_dec_bl in H1.
  auto.
Qed.
