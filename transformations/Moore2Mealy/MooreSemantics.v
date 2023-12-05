Require Import String.
Require Import List.

Require Import transformations.Moore2Mealy.Moore.
Require Import core.Model.
Require Import core.utils.Utils.

Import Id Glue.

Definition initialState (m: M) : option State_t :=
    find_lift (get_E_data State_K) (fun s => NodeId_beq (Id "S0") s.(State_id)) m.(modelElements).

Definition State_outTransitions (m: M) (s: State_t) : list Transition_t :=
    filter_lift 
      (get_E_data Transition_K) 
      (fun t => 
         match (getTransition_source m t) with
         | Some s' => State_t_beq s s' (* fixme : compare only the ids ? *)
         | None => false
         end)
      m.(Model.modelElements).

Definition State_acceptTransition (m: M) (s: State_t) (i: string) : option Transition_t :=
    find (fun t => eqb i t.(Transition_input)) (State_outTransitions m s).

Definition search (m: M) (current: State_t) i :=
  match State_acceptTransition m current i with
    | Some t =>  getTransition_target m t
    | None => None
  end.

Fixpoint executeFromState (m: M) (current: State_t) (remainingInput: list string) : option (list string) :=
  match remainingInput with 
   | i :: inputs => 
       match search m current i with
        | Some s => 
            match executeFromState m s inputs with
            | Some r => Some (s.(State_output) :: r)
            | None => None
            end
        | None => None
       end
   | nil => Some nil 
  end.

Definition execute (m: M) (input: list string) : option (list string) :=
    match initialState m with 
    | Some s => executeFromState m s input
    | None => None
    end.


(* get_Transition_target          getTransition_source *)
(*                 \               /                   *)
(*                  \             /                    *)
(*                   \          State_outTransitions   *)
(*                    \         /                      *)             
(*                     \       /                       *)
(*                      \    State_acceptTransition    *)
(*                       \   /                         *)  
(*                        \ /                          *)
(*                       search                        *)
(*                        /                            *)
(*                       /                             *)
(*     initialState    executeFromState                *)
(*                 \   /                               *)
(*                  \ /                                *)
(*                execute                              *)


(** Some tactics *)

Lemma State_out_transitions_inv m s t :
  List.In t (State_outTransitions m s) ->
  List.In (Transition t) (Model.modelElements m)
  /\ getTransition_source m t = Some s.
Proof.
  intro H.
  unfold State_outTransitions in H.
  apply OptionListUtils.filter_lift_in in H.
  destruct H as (? & ? & ? & ?).                   
  PropUtils.destruct_match_H H1 ; [ | discriminate H1]. 
  apply internal_State_t_dec_bl in H1. subst s0.    
  destruct x ;[discriminate H0 | PropUtils.inj H0]. (* monadInv *) 
  auto.
Qed.

Lemma in_State_outTransitions (m:Moore.M) s t :
  List.In (Transition t) (Model.modelElements m) ->
  getTransition_source m t = Some s ->
  List.In t (State_outTransitions m s).
Proof.
  intros.
  unfold State_outTransitions.
  apply OptionListUtils.filter_lift_in.
  exists (Transition t).
  split ; [ assumption | ].
  split ; [ reflexivity | ].
  rewrite H0.
  apply internal_State_t_dec_lb.
  reflexivity.
Qed.

Lemma State_acceptTransition_inv :
  forall m s1 i t,
    State_acceptTransition m s1 i = Some t -> 
    List.In t (State_outTransitions m s1) /\
      i = Transition_input t.
Proof.
  intros.
  unfold State_acceptTransition in H.
  destruct (List.find_some _ _ H).
  apply String.eqb_eq in H1.
  split ; assumption.
Qed.

Lemma search_inv :
  forall m s i r,
    search m s i = Some r ->
    exists t, 
      State_acceptTransition m s i = Some t /\
        getTransition_target m t = Some r.
Proof.
  unfold search ; intros.
  OptionUtils.monadInv H.
  eauto.
Qed.


Lemma search_in_left m :
  WF_transition_source_glue_r_exists m ->
  forall s1 a s2,
  search m s1 a = Some s2 ->
  List.In (State s1) m.(Model.modelElements).
Proof.
  intro WF.
  intros.
  destruct (search_inv _ _ _ _ H) as (?&?&?).
  destruct (State_acceptTransition_inv _ _ _ _ H0).
  destruct (State_out_transitions_inv _ _ _ H2).
  apply getTransition_source_inv in H5.
  subst.
  eapply WF in H5. exact H5.
Qed.

(* fixme : move-me *)
Definition WF_targetLink_target_in (m:Moore.M) :=
      forall lk, 
        In (TransitionTarget lk) m.(modelLinks) ->
        In (State lk.(trg)) m.(modelElements).

Lemma search_in_right m :
  WF_targetLink_target_in m ->
  forall s1 a s2,
  search m s1 a = Some s2 ->
  List.In (State s2) m.(Model.modelElements).
Proof.
  intro WF.
  intros.
  destruct (search_inv _ _ _ _ H) as (?&?&?).
  apply getTransition_target_inv in H1.
  apply WF in H1. exact H1.
Qed.


(** Some tests *)

Require Import transformations.Moore2Mealy.tests.sampleMoore.

Compute execute InputModel ("A"::nil).      (* "b"  *)
Compute execute InputModel ("A"::"B"::nil). (* "bb" *)
Compute execute InputModel ("B"::nil).      (* None *)
Compute execute InputModel ("A"::"A"::nil). (* None *)



