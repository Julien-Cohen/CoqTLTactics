(** Imports Native *)
Require Import 
  String Bool List PeanoNat EqNat.

(** Imports CoqTL *)
From core 
  Require Import 
  utils.Utils Metamodel modeling.ModelingMetamodel Model.

Require Import 
  Moore2Mealy.Id Glue.

(** Base types for elements *)
Record State_t := { State_id : NodeId }.
Scheme Equality for State_t.


Record Transition_t := { Transition_id : nat ; Transition_input : string ; Transition_output : string }.
Scheme Equality for Transition_t.




(** Data types for element (to build models) *)
Inductive Element : Set :=
  | State : State_t -> Element
  | Transition : Transition_t -> Element
.
Scheme Equality for Element.


(** Data types for link (to build models) *)
Inductive Link : Set :=
  | TransitionSource : Glue Transition_t State_t -> Link
  | TransitionTarget : Glue Transition_t State_t -> Link
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
  elements_eq_dec := Element_eq_dec ;
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
Definition getTransition_sourceOnLinks (t : Transition_t) (l : list Link) : option (State_t) :=
  option_map 
    trg 
    (find_lift 
       (get_L_data Transition_source_K) 
       (fun s => Transition_t_beq s.(src) t)
       l
    ). 


Definition getTransition_source (m : M) (t : Transition_t) : option (State_t) :=
  getTransition_sourceOnLinks t m.(modelLinks).


Definition getTransition_targetOnLinks (t : Transition_t) (l : list Link) : option (State_t) :=
  option_map 
    trg 
    (find_lift 
       (get_L_data Transition_target_K) 
       (fun s => Transition_t_beq s.(src) t)
       l
    ).



Definition getTransition_target (m : M) (t : Transition_t) : option (State_t) :=
  getTransition_targetOnLinks t m.(modelLinks).


(** *** Well formed models : high-level properties *)

(** Transitions have valid source and destination states. *) 

(* not used ? *)
Definition WF_transition_target_exists (m:M) : Prop :=
  forall t, 
    List.In (Transition t) m.(modelElements) ->
    SUCCESS ( getTransition_target m t ).


(* not used ? *)
Definition WF_transition_source_exists (m:M) : Prop :=
  forall t, 
    List.In (Transition t) m.(modelElements) ->
    SUCCESS ( getTransition_source m t ).


Definition WF_transition_target_glue_r_exists (m:M) : Prop :=
  forall lk,
    List.In (TransitionTarget lk) m.(modelLinks) ->
    List.In (State lk.(trg)) m.(modelElements).

Definition WF_transition_source_glue_r_exists (m:Mealy.M) :=
      forall lk, 
        In (TransitionSource lk) m.(modelLinks) ->
        In (State lk.(trg)) m.(modelElements).

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


Lemma In_state :
 forall (m:Mealy.M) e,
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
    destruct e2 ; [ unfold get_E_data in G ; injection G ; intro ; subst| discriminate G]. 
    assumption.
  }
Qed.

Lemma In_transition :
 forall (m:Mealy.M) e,
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
  forall (m:Mealy.M) e,
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
  forall (m:Mealy.M) e,
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
  let lk := {|  src := t ;  trg := s |} in
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
  let lk := {| trg := s ; src := t |} in 
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



