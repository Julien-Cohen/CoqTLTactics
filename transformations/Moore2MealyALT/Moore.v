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

(** Base types for elements *)
Record State_t := { State_name : string ; State_output : string }.
Scheme Equality for State_t.
Lemma lem_State_t_beq_id : forall (e1 e2 : State_t), State_t_beq e1 e2 = true -> e1 = e2.
Proof. exact internal_State_t_dec_bl. Qed. 
Lemma lem_State_t_beq_refl : forall (e : State_t), State_t_beq e e = true.
Proof. intro ; apply internal_State_t_dec_lb ; auto. Qed. 

Record Transition_t := { Transition_id : nat ; Transition_input : string }.
Scheme Equality for Transition_t.
Lemma lem_Transition_t_beq_id : forall (e1 e2 : Transition_t), Transition_t_beq e1 e2 = true -> e1 = e2.
Proof. exact internal_Transition_t_dec_bl. Qed. 
Lemma lem_Transition_t_beq_refl : forall (e : Transition_t), Transition_t_beq e e = true.
Proof. intro ; apply internal_Transition_t_dec_lb ; auto. Qed. 



(** Base types for links *)
Record Transition_source_t := { Transition_source_t_source : Transition_t ; Transition_source_t_target : State_t }.
Scheme Equality for Transition_source_t.
Lemma lem_Transition_source_t_beq_id : forall (e1 e2 : Transition_source_t), Transition_source_t_beq e1 e2 = true -> e1 = e2.
Proof. exact internal_Transition_source_t_dec_bl. Qed. 
Lemma lem_Transition_source_t_beq_refl : forall (e : Transition_source_t), Transition_source_t_beq e e = true.
Proof. intro ; apply internal_Transition_source_t_dec_lb ; auto. Qed. 


Record Transition_target_t := { Transition_target_t_source : Transition_t ; Transition_target_t_target : State_t }.
Scheme Equality for Transition_target_t.
Lemma lem_Transition_target_t_beq_id : forall (e1 e2 : Transition_target_t), Transition_target_t_beq e1 e2 = true -> e1 = e2.
Proof. exact internal_Transition_target_t_dec_bl. Qed. 
Lemma lem_Transition_target_t_beq_refl : forall (e : Transition_target_t), Transition_target_t_beq e e = true.
Proof. intro ; apply internal_Transition_target_t_dec_lb ; auto. Qed. 



(** Data types for element (to build models) *)
Inductive Element : Set :=
  | StateElement : State_t -> Element
  | TransitionElement : Transition_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  | Transition_sourceLink : Transition_source_t -> Link
  | Transition_targetLink : Transition_target_t -> Link
.
Scheme Equality for Link.

(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
  | State_K
  | Transition_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
  | Transition_source_K
  | Transition_target_K
.
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
  match k with
  | Transition_source_K => Transition_source_t
  | Transition_target_K => Transition_target_t
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | Transition_source_K => Transition_sourceLink
  | Transition_target_K => Transition_targetLink
  end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (Transition_source_K, Transition_sourceLink v)  => Some v
  | (Transition_target_K, Transition_targetLink v)  => Some v
  | (_ , _) => None
  end.

(** Typeclass Instance *)
Definition MM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eqdec := Element_beq ;
  links_eqdec := Link_beq
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
Fixpoint getTransition_sourceOnLinks (t : Transition_t) (l : list Link) : option (State_t) :=
 match l with
  | (Transition_sourceLink x) :: l1 =>
    if Transition_t_beq x.(Transition_source_t_source) t
      then (Some x.(Transition_source_t_target))
      else getTransition_sourceOnLinks t l1
  | _ :: l1 => getTransition_sourceOnLinks t l1
  | nil => None
 end.

Definition getTransition_source (m : M) (t : Transition_t) : option (State_t) :=
  getTransition_sourceOnLinks t m.(modelLinks).


Fixpoint getTransition_targetOnLinks (t : Transition_t) (l : list Link) : option (State_t) :=
 match l with
  | (Transition_targetLink x) :: l1 =>
    if Transition_t_beq x.(Transition_target_t_source) t
      then (Some x.(Transition_target_t_target))
      else getTransition_targetOnLinks t l1
  | _ :: l1 => getTransition_targetOnLinks t l1
  | nil => None
 end.


Definition getTransition_target (m : M) (t : Transition_t) : option (State_t) :=
  getTransition_targetOnLinks t m.(modelLinks).

(* FIXME : generate-me*)
Definition WF1 (m:M) : Prop :=
  forall t, 
    List.In (TransitionElement t) m.(modelElements) ->
    SUCCESS ( getTransition_target m t ).

(* FIXME : generate-me*)
Definition WF2 (m:M) :Prop :=
  forall t, 
    List.In (TransitionElement t) m.(modelElements) ->
    SUCCESS ( getTransition_source m t ).

(** Useful lemmas *)
Lemma Moore_invert : 
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

(** Manual addition *)
Definition Transition_getSourceObject (t : Transition_t) (m : M) : option (Element) :=
match getTransition_source m t with
  | Some st_arg => Some (StateElement st_arg) 
  | None => None
  end.

Definition Transition_getTargetObject (tr_arg : Transition_t) (m : M) : option (Element) :=
  match getTransition_target m tr_arg with
  | Some st_arg => Some (StateElement st_arg) 
  | None => None
  end.


(** For user *)
Definition maybeBuildTransitionSource (tr_arg: Transition_t) (so_arg: option (State_t)) : option Transition_source_t :=
  match tr_arg, so_arg with
  | tr_arg_succ, Some so_arg_succ => Some (Build_Transition_source_t tr_arg_succ so_arg_succ)
  | _, _ => None
  end.


Definition maybeBuildTransitionTarget (tr_arg: Transition_t) (ta_arg: option (State_t)) : option Transition_target_t :=
  match tr_arg, ta_arg with
  | tr_arg_succ, Some ta_arg_succ => Some (Build_Transition_target_t tr_arg_succ ta_arg_succ)
  | _, _ => None
  end.

