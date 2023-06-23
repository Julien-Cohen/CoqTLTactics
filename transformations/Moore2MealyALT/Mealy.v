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
Require        core.Tactics.

Require Import Id.

(** Base types for elements *)
Record State_t := { State_name : NodeId }.
Scheme Equality for State_t.
Lemma lem_State_t_beq_id : forall (e1 e2 : State_t), State_t_beq e1 e2 = true -> e1 = e2.
Proof. exact internal_State_t_dec_bl. Qed. 
Lemma lem_State_t_beq_refl : forall (e : State_t), State_t_beq e e = true.
Proof. intro ; apply internal_State_t_dec_lb ; auto. Qed. 


Record Transition_t := { Transition_source : NodeId ; Transition_input : string ; Transition_output : string ; Transition_dest : NodeId }.
Scheme Equality for Transition_t.
Lemma lem_Transition_t_beq_id : forall (e1 e2 : Transition_t), Transition_t_beq e1 e2 = true -> e1 = e2.
Proof. exact internal_Transition_t_dec_bl. Qed. 
Lemma lem_Transition_t_beq_refl : forall (e : Transition_t), Transition_t_beq e e = true.
Proof. intro ; apply internal_Transition_t_dec_lb ; auto. Qed. 



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
. (* Empty *)
Scheme Equality for Link.

(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
  | State_K
  | Transition_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
. (* Empty *)
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
  match t with end.

(** Typeclass Instance *)
Definition MM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eqdec := Element_beq ;
  links_eqdec := Link_beq
|}.


#[export]
Instance MealyElementDenotation : Denotation Element ElementKind :=
{
  denoteDatatype := getTypeByEKind ;
  unbox := get_E_data ;
  constructor := lift_EKind ;
}.


#[export]
Instance MealyLinkDenotation : Denotation Link LinkKind :=
{
  denoteDatatype := getTypeByLKind ;
  unbox := get_L_data ;
  constructor := lift_LKind ;
}.


#[export]
Instance MMM : ModelingMetamodel MM :=
{
  elements := MealyElementDenotation ;
  links := MealyLinkDenotation ;
}.


Definition M := Model MM.

(** General functions (used in transformations) *)

Definition getTransition_source (m : M) (t : Transition_t) : option (State_t) :=
  find_lift (get_E_data State_K) (fun s => NodeId_beq t.(Transition_source) s.(State_name)) m.(modelElements).  


Definition getTransition_target (m : M) (t : Transition_t) : option (State_t) :=
  find_lift (get_E_data State_K) (fun s => NodeId_beq t.(Transition_dest) s.(State_name)) m.(modelElements).  

(* FIXME : generate-me*)
Definition WF1 (m:M) : Prop :=
  forall t, 
    List.In (TransitionElement t) m.(modelElements) ->
    SUCCESS ( getTransition_target m t ).

(* FIXME : generate-me*)
Definition WF2 (m:M) : Prop :=
  forall t, 
    List.In (TransitionElement t) m.(modelElements) ->
    SUCCESS ( getTransition_source m t ).

(** Useful lemmas *)
Lemma Mealy_invert : 
  forall (k: ElementKind) (t1 t2: getTypeByEKind k),
    constructor k t1 = constructor k t2 -> t1 = t2.
Proof. intro k ; destruct k ; simpl; congruence.  Qed. 


Lemma Element_dec : 
  forall (a: Element),
(instanceof State_K a) = true\/(instanceof Transition_K a) = true
.
Proof. destruct a ; auto. Qed. 


Lemma StateElement_cast :
  forall x y,
    unbox State_K x = return y -> StateElement y = x.
Proof. destruct x ; destruct y ; compute ; congruence. Qed. 


Lemma TransitionElement_cast :
  forall x y,
    unbox Transition_K x = return y -> TransitionElement y = x.
Proof. destruct x ; destruct y ; compute ; congruence. Qed. 


(** Added Manually *)

Definition getTransition_sourceObject (t : Transition_t) (m : M) : option Element :=
  match getTransition_source m t with
  | Some st_arg => Some (lift_EKind State_K st_arg) 
  | _ => None
  end.

Definition getTransition_TargetObject (tr_arg : Transition_t) (m : M) : option Element :=
  match getTransition_target m tr_arg with
  | Some st_arg => Some (lift_EKind State_K st_arg) 
  | _ => None
  end.


