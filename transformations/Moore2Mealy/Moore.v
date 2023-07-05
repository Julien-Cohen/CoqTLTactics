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

Require Import Glue.

Require Import Moore2Mealy.Id.

(** Base types for elements *)
Record State_t := { State_id : NodeId ; State_output : string }.
Scheme Equality for State_t.

Record Transition_t := { Transition_id : nat ; Transition_input : string }.
Scheme Equality for Transition_t.


(** Base types for links *)
Definition Transition_source_t := @Glue Transition_t State_t.

Definition Transition_target_t := @Glue Transition_t State_t.


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

Definition Link_beq (a:Link) (b:Link) : bool.
  destruct a eqn:? , b eqn:?.
  + unfold Transition_source_t in *.
    Set Printing Implicit.
    apply (Glue.Glue_beq _ _ Transition_t_beq State_t_beq t t0).
  + exact false.
  + exact false.
  + apply (Glue.Glue_beq _ _ Transition_t_beq State_t_beq t t0).
Defined.

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
Definition getTransition_sourceOnLinks (t : Transition_t) (l : list Link) : option (State_t) :=
  option_map 
    rglue 
    (find_lift 
       (get_L_data Transition_source_K) 
       (fun s => Transition_t_beq s.(lglue) t)
       l
    ).


Definition getTransition_source (m : M) (t : Transition_t) : option (State_t) :=
  getTransition_sourceOnLinks t m.(modelLinks).

Definition getTransition_targetOnLinks (t : Transition_t) (l : list Link) : option (State_t) :=
  option_map 
    rglue 
    (find_lift 
       (get_L_data Transition_target_K) 
       (fun s => Transition_t_beq s.(lglue) t)
       l
    ).



Definition getTransition_target (m : M) (t : Transition_t) : option (State_t) :=
  getTransition_targetOnLinks t m.(modelLinks).

(* FIXME : generate-me*)
Definition WF_target (m:M) : Prop :=
  forall t, 
    List.In (TransitionElement t) m.(modelElements) ->
    SUCCESS ( getTransition_target m t ).

(* FIXME : generate-me*)
Definition WF_source (m:M) : Prop :=
  forall t, 
    List.In (TransitionElement t) m.(modelElements) ->
    SUCCESS ( getTransition_source m t ).

(* FIXME : generate-me*)
Definition WF_source_lglue (m:M) : Prop :=
  forall lk,
    List.In (Transition_sourceLink lk) m.(modelLinks) ->
    List.In (TransitionElement lk.(lglue)) m.(modelElements).

(* FIXME : generate-me*)
Definition WF_source_rglue (m:M) : Prop :=
  forall lk,
    List.In (Transition_sourceLink lk) m.(modelLinks) ->
    List.In (StateElement lk.(rglue)) m.(modelElements).

(* FIXME : generate-me*)
Definition WF_target_lglue (m:M) : Prop :=
  forall lk,
    List.In (Transition_targetLink lk) m.(modelLinks) ->
    List.In (TransitionElement lk.(lglue)) m.(modelElements).

(* FIXME : generate-me*)
Definition WF_target_rglue (m:M) : Prop :=
  forall lk,
    List.In (Transition_targetLink lk) m.(modelLinks) ->
    List.In (StateElement lk.(rglue)) m.(modelElements).

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
  end. (* option_map *)

Definition Transition_getTargetObject (tr_arg : Transition_t) (m : M) : option (Element) :=
  match getTransition_target m tr_arg with
  | Some st_arg => Some (StateElement st_arg) 
  | None => None
  end. (* option_map *)


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


Lemma In_transition_sourceLink : 
  forall (m:Moore.M) e,
         List.In (Transition_sourceLink e) (Model.modelLinks m) <-> List.In e
    (OptionListUtils.lift_list (get_L_data Transition_source_K)
       (Model.modelLinks m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (Transition_sourceLink e). auto.
  }  
  {
    apply OptionListUtils.In_lift in H.
    destruct H as (e2 & (G & IN2)).
    destruct e2 ; [ PropUtils.inj G | discriminate G]. 
    assumption.
  }
Qed.

Lemma In_transition_targetLink : 
  forall (m:Moore.M) e,
         List.In (Transition_targetLink e) (Model.modelLinks m) <-> List.In e
    (OptionListUtils.lift_list (get_L_data Transition_target_K)
       (Model.modelLinks m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (Transition_targetLink e). auto.
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
  let lk := {| lglue := t ; rglue := s |} 
  in
  List.In (Transition_sourceLink lk) m.(Model.modelLinks).
  (*    List.In (StateElement s) (Model.modelElements m). *)
Proof.
  unfold getTransition_source.
  generalize (modelLinks m).
  unfold getTransition_sourceOnLinks.
  intros links H.
  OptionUtils.monadInv H.
  apply OptionListUtils.find_lift_some in H.
  destruct H as (?&?&?&?).
  destruct x ; [ PropUtils.inj H | discriminate H].
  apply internal_Transition_t_dec_bl in H1 ; subst.
  destruct g ; auto.
Qed.


Lemma getTransition_target_inv m t s : 
  getTransition_target m t = Some s -> 
  let lk := {| rglue := s ; lglue := t |} 
  in 
    In (Transition_targetLink lk)  m.(Model.modelLinks).
Proof.
  unfold getTransition_target.
  generalize (modelLinks m).
  unfold getTransition_targetOnLinks.
  intros links H.
  OptionUtils.monadInv H.
  apply OptionListUtils.find_lift_some in H.
  destruct H as (?&?&?&?).
  destruct x ; [ discriminate H | PropUtils.inj H ].
  apply internal_Transition_t_dec_bl in H1 ; subst.
  destruct g ; auto.
Qed.


(** For user *)
Definition maybeBuildTransitionSource (tr_arg: Transition_t) (so_arg: option (State_t)) : option Transition_source_t :=
  option_map (@Build_Glue _ _ tr_arg) so_arg.

Definition maybeBuildTransitionTarget (tr_arg: Transition_t) (ta_arg: option (State_t)) : option Transition_target_t :=
  option_map (@Build_Glue _ _ tr_arg) ta_arg.
 

