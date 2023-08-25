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



(** Data types for element (to build models) *)
Inductive Element : Set :=
  | State : State_t -> Element
  | Transition : Transition_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  | TransitionSource : @Glue Transition_t State_t -> Link
  | TransitionTarget : @Glue Transition_t State_t -> Link
.


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
  | State_K => State
  | Transition_K => Transition
  end.


Definition get_E_data (k : ElementKind) (c : Element) : option (getTypeByEKind k) :=
  match (k,c) as e return (option (getTypeByEKind (fst e))) with
  | (State_K, State v)  => Some v
  | (Transition_K, Transition v)  => Some v
  | (_ , _) => None
  end.


Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with
  | Transition_source_K => @Glue Transition_t State_t
  | Transition_target_K => @Glue Transition_t State_t
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | Transition_source_K => TransitionSource
  | Transition_target_K => TransitionTarget
  end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (Transition_source_K, TransitionSource v)  => Some v
  | (Transition_target_K, TransitionTarget v)  => Some v
  | (_ , _) => None
  end.

(** Typeclass Instance *)
Definition MM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eqdec := Element_beq ;
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
    r_glue 
    (find_lift 
       (get_L_data Transition_source_K) 
       (fun s => Transition_t_beq s.(l_glue) t)
       l
    ).


Definition getTransition_source (m : M) (t : Transition_t) : option (State_t) :=
  getTransition_sourceOnLinks t m.(modelLinks).

Definition getTransition_targetOnLinks (t : Transition_t) (l : list Link) : option (State_t) :=
  option_map 
    r_glue 
    (find_lift 
       (get_L_data Transition_target_K) 
       (fun s => Transition_t_beq s.(l_glue) t)
       l
    ).



Definition getTransition_target (m : M) (t : Transition_t) : option (State_t) :=
  getTransition_targetOnLinks t m.(modelLinks).


(** *** Well formed models : high-level properties *)

(** Transitions have valid source and destination states. *) 

Definition WF_transition_target_exists (m:M) : Prop :=
  forall t, 
    List.In (Transition t) m.(modelElements) ->
    SUCCESS ( getTransition_target m t ).

Definition WF_transition_source_exists (m:M) : Prop :=
  forall t, 
    List.In (Transition t) m.(modelElements) ->
    SUCCESS ( getTransition_source m t ).


(** *** Well formed models : low-level properties *)

(** Links glue only valid states with valid transitions *)

Definition WF_transition_source_glue_l_exists (m:M) : Prop :=
  forall lk,
    List.In (TransitionSource lk) m.(modelLinks) ->
    List.In (Transition lk.(l_glue)) m.(modelElements).

(* lorsque les sources de transitions existent, 
   les glues pour ces transitions existent. *)
Lemma tmp : 
  forall m, 
    WF_transition_source_exists m ->
    forall t, 
      List.In (Transition t) m.(modelElements) -> 
      exists g, 
        List.In (TransitionSource g) m.(modelLinks) /\ g.(l_glue) = t.
Proof.
  unfold WF_transition_source_exists.
  intros m H1 t H2.
  specialize (H1 t H2).
  destruct H1 as (s & H1).
  unfold getTransition_source in H1.
  unfold  getTransition_sourceOnLinks in H1.
  monadInv H1.
  simpl in g.
  apply find_lift_some in H1.
  destruct H1 as (A&H3&H4&H5).
  apply internal_Transition_t_dec_bl in H5.
  destruct A  ; unfold get_L_data in H3 ; [ inj H3| discriminate H3 ].
  eauto.
Qed.    


Definition WF_transition_source_glue_r_exists (m:M) : Prop :=
  forall lk,
    List.In (TransitionSource lk) m.(modelLinks) ->
    List.In (State lk.(r_glue)) m.(modelElements).


Definition WF_transition_target_glue_l_exists (m:M) : Prop :=
  forall lk,
    List.In (TransitionTarget lk) m.(modelLinks) ->
    List.In (Transition lk.(l_glue)) m.(modelElements).


Definition WF_transition_target_glue_r_exists (m:M) : Prop :=
  forall lk,
    List.In (TransitionTarget lk) m.(modelLinks) ->
    List.In (State lk.(r_glue)) m.(modelElements).


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


Lemma State_cast :
  forall x y,
    unbox State_K x = return y -> State y = x.
Proof. destruct x ; destruct y ; compute ; congruence. Qed. 


Lemma Transition_cast :
  forall x y,
    unbox Transition_K x = return y -> Transition y = x.
Proof. destruct x ; destruct y ; compute ; congruence. Qed. 

(** Manual addition *)
Definition Transition_getSourceObject (t : Transition_t) (m : M) : option (Element) :=
  option_map State (getTransition_source m t).

Definition Transition_getTargetObject (tr_arg : Transition_t) (m : M) : option (Element) :=
  option_map State (getTransition_target m tr_arg).


Lemma In_state : forall (m:Moore.M) e,
         List.In (State e) (Model.modelElements m) <-> List.In e
    (OptionListUtils.lift_list (get_E_data State_K)
       (Model.modelElements m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (State e). auto.
  }  
  {
    apply OptionListUtils.In_lift in H.
    destruct H as (e2 & (G & IN2)).
    destruct e2 ; [ PropUtils.inj G| discriminate G]. 
    assumption.
  }
Qed.


Lemma In_transition : forall (m:Moore.M) e,
         List.In (Transition e) (Model.modelElements m) <-> List.In e
    (OptionListUtils.lift_list (get_E_data Transition_K)
       (Model.modelElements m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (Transition e). auto.
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
         List.In (TransitionSource e) (Model.modelLinks m) <-> List.In e
    (OptionListUtils.lift_list (get_L_data Transition_source_K)
       (Model.modelLinks m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (TransitionSource e). auto.
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
         List.In (TransitionTarget e) (Model.modelLinks m) <-> List.In e
    (OptionListUtils.lift_list (get_L_data Transition_target_K)
       (Model.modelLinks m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (TransitionTarget e). auto.
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
  let lk := {| l_glue := t ; r_glue := s |} 
  in
  List.In (TransitionSource lk) m.(Model.modelLinks).
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
  let lk := {| r_glue := s ; l_glue := t |} 
  in 
    In (TransitionTarget lk)  m.(Model.modelLinks).
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
Definition maybeBuildTransitionSource (tr_arg: Transition_t) (so_arg: option (State_t)) : option (@Glue Transition_t State_t) :=
  option_map (@Build_Glue _ _ tr_arg) so_arg.

Definition maybeBuildTransitionTarget (tr_arg: Transition_t) (ta_arg: option (State_t)) : option (@Glue Transition_t State_t) :=
  option_map (@Build_Glue _ _ tr_arg) ta_arg.
 

