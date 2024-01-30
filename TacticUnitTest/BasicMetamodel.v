(** Basic graphs *)

(** Imports Native *)
Require Import String Bool List PeanoNat EqNat.

(** Imports CoqTL *)
From core 
  Require Import utils.Utils Metamodel modeling.ModelingMetamodel Model.

Require Import Glue (*UnitTest.Id*).

(** Base types for elements *)
Record Node_t := { Node_id : nat }.
Scheme Equality for Node_t.

Record Arrow_t := { Arrow_id : nat }.
Scheme Equality for Arrow_t.



(** Data types for element (to build models) *)
Inductive Element : Set :=
  | Node : Node_t -> Element
  | Arrow : Arrow_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  | ArrowSource : Glue Arrow_t Node_t -> Link
  | ArrowTarget : Glue Arrow_t Node_t -> Link
.


(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
  | Node_K
  | Arrow_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
  | Arrow_source_K
  | Arrow_target_K
.
Scheme Equality for LinkKind.

(** Reflective functions (typing : correspondence between abstract types (kinds) and model data) *)
Definition getTypeByEKind (k : ElementKind) : Set :=
  match k with
  | Node_K => Node_t
  | Arrow_K => Arrow_t
  end.


Definition lift_EKind k : (getTypeByEKind k) -> Element := 
  match k with
  | Node_K => Node
  | Arrow_K => Arrow
  end.


Definition get_E_data (k : ElementKind) (c : Element) : option (getTypeByEKind k) :=
  match (k,c) as e return (option (getTypeByEKind (fst e))) with
  | (Node_K, Node v)  => Some v
  | (Arrow_K, Arrow v)  => Some v
  | (_ , _) => None
  end.


Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with
  | Arrow_source_K => @Glue Arrow_t Node_t
  | Arrow_target_K => @Glue Arrow_t Node_t
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | Arrow_source_K => ArrowSource
  | Arrow_target_K => ArrowTarget
  end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (Arrow_source_K, ArrowSource v)  => Some v
  | (Arrow_target_K, ArrowTarget v)  => Some v
  | (_ , _) => None
  end.

(** Typeclass Instance *)
Definition MM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eq_dec := Element_eq_dec
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
Definition getArrow_sourceOnLinks (t : Arrow_t) (l : list Link) : option (Node_t) :=
  option_map 
    trg 
    (find_lift 
       (get_L_data Arrow_source_K) 
       (fun s => Arrow_t_beq s.(src) t)
       l
    ).


Definition getArrow_source (m : M) (t : Arrow_t) : option (Node_t) :=
  getArrow_sourceOnLinks t m.(modelLinks).

Definition getArrow_targetOnLinks (t : Arrow_t) (l : list Link) : option (Node_t) :=
  option_map 
    trg 
    (find_lift 
       (get_L_data Arrow_target_K) 
       (fun s => Arrow_t_beq s.(src) t)
       l
    ).



Definition getArrow_target (m : M) (t : Arrow_t) : option (Node_t) :=
  getArrow_targetOnLinks t m.(modelLinks).


(** *** Well formed models : high-level properties *)

(** Arrows have valid source and destination states. *) 

Definition WF_transition_target_exists (m:M) : Prop :=
  forall t, 
    List.In (Arrow t) m.(modelElements) ->
    SUCCESS ( getArrow_target m t ).

Definition WF_transition_source_exists (m:M) : Prop :=
  forall t, 
    List.In (Arrow t) m.(modelElements) ->
    SUCCESS ( getArrow_source m t ).


(** *** Well formed models : low-level properties *)

(** Links glue only valid states with valid transitions *)

Definition WF_transition_source_glue_l_exists (m:M) : Prop :=
  forall lk,
    List.In (ArrowSource lk) m.(modelLinks) ->
    List.In (Arrow lk.(src)) m.(modelElements).

(* lorsque les sources de transitions existent, 
   les glues pour ces transitions existent. *)
Lemma tmp : 
  forall m, 
    WF_transition_source_exists m ->
    forall t, 
      List.In (Arrow t) m.(modelElements) -> 
      exists g, 
        List.In (ArrowSource g) m.(modelLinks) /\ g.(src) = t.
Proof.
  unfold WF_transition_source_exists.
  intros m H1 t H2.
  specialize (H1 t H2).
  destruct H1 as (s & H1).
  unfold getArrow_source in H1.
  unfold  getArrow_sourceOnLinks in H1.
  monadInv H1.
  simpl in g.
  apply find_lift_some in H1.
  destruct H1 as (A&H3&H4&H5).
  apply internal_Arrow_t_dec_bl in H5.
  destruct A  ; unfold get_L_data in H3 ; [ inj H3| discriminate H3 ].
  eauto.
Qed.    


Definition WF_transition_source_glue_r_exists (m:M) : Prop :=
  forall lk,
    List.In (ArrowSource lk) m.(modelLinks) ->
    List.In (Node lk.(trg)) m.(modelElements).


Definition WF_transition_target_glue_l_exists (m:M) : Prop :=
  forall lk,
    List.In (ArrowTarget lk) m.(modelLinks) ->
    List.In (Arrow lk.(src)) m.(modelElements).


Definition WF_transition_target_glue_r_exists (m:M) : Prop :=
  forall lk,
    List.In (ArrowTarget lk) m.(modelLinks) ->
    List.In (Node lk.(trg)) m.(modelElements).


(** Manual addition *)
Definition Arrow_getSourceObject (t : Arrow_t) (m : M) : option (Element) :=
  option_map Node (getArrow_source m t).

Definition Arrow_getTargetObject (tr_arg : Arrow_t) (m : M) : option (Element) :=
  option_map Node (getArrow_target m tr_arg).


Lemma In_state : forall (m:M) e,
         List.In (Node e) (Model.modelElements m) <-> List.In e
    (OptionListUtils.lift_list (get_E_data Node_K)
       (Model.modelElements m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (Node e). auto.
  }  
  {
    apply OptionListUtils.In_lift in H.
    destruct H as (e2 & (G & IN2)).
    destruct e2 ; [ PropUtils.inj G| discriminate G]. 
    assumption.
  }
Qed.


Lemma In_transition : forall (m:M) e,
         List.In (Arrow e) (Model.modelElements m) <-> List.In e
    (OptionListUtils.lift_list (get_E_data Arrow_K)
       (Model.modelElements m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (Arrow e). auto.
  }  
  {
    apply OptionListUtils.In_lift in H.
    destruct H as (e2 & (G & IN2)).
    destruct e2 ; [ discriminate G | PropUtils.inj G]. 
    assumption.
  }
Qed.


Lemma In_transition_sourceLink : 
  forall (m:M) e,
         List.In (ArrowSource e) (Model.modelLinks m) <-> List.In e
    (OptionListUtils.lift_list (get_L_data Arrow_source_K)
       (Model.modelLinks m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (ArrowSource e). auto.
  }  
  {
    apply OptionListUtils.In_lift in H.
    destruct H as (e2 & (G & IN2)).
    destruct e2 ; [ PropUtils.inj G | discriminate G]. 
    assumption.
  }
Qed.

Lemma In_transition_targetLink : 
  forall (m:M) e,
         List.In (ArrowTarget e) (Model.modelLinks m) <-> List.In e
    (OptionListUtils.lift_list (get_L_data Arrow_target_K)
       (Model.modelLinks m)).
Proof.
  intros m e.
  split ; intro H.
  {
    apply OptionListUtils.In_lift.
    exists (ArrowTarget e). auto.
  }  
  {
    apply OptionListUtils.In_lift in H.
    destruct H as (e2 & (G & IN2)).
    destruct e2 ; [ discriminate G | PropUtils.inj G]. 
    assumption.
  }
Qed.


Lemma getArrow_source_inv m t s : 
  getArrow_source m t = Some s ->
  let lk := {| src := t ; trg := s |} 
  in
  List.In (ArrowSource lk) m.(Model.modelLinks).
Proof.
  unfold getArrow_source.
  generalize (modelLinks m).
  unfold getArrow_sourceOnLinks.
  intros links H.
  OptionUtils.monadInv H.
  apply OptionListUtils.find_lift_some in H.
  destruct H as (?&?&?&?).
  destruct x ; [ PropUtils.inj H | discriminate H].
  apply internal_Arrow_t_dec_bl in H1 ; subst.
  destruct g ; auto.
Qed.


Lemma getArrow_target_inv m t s : 
  getArrow_target m t = Some s -> 
  let lk := {| trg := s ; src := t |} 
  in 
    In (ArrowTarget lk)  m.(Model.modelLinks).
Proof.
  unfold getArrow_target.
  generalize (modelLinks m).
  unfold getArrow_targetOnLinks.
  intros links H.
  OptionUtils.monadInv H.
  apply OptionListUtils.find_lift_some in H.
  destruct H as (?&?&?&?).
  destruct x ; [ discriminate H | PropUtils.inj H ].
  apply internal_Arrow_t_dec_bl in H1 ; subst.
  destruct g ; auto.
Qed.


