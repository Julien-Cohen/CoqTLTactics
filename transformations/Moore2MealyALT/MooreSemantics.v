Require Import String.
Require Import List.

Require Import transformations.Moore2MealyALT.Moore.
Require Import core.Model.
Require Import core.utils.Utils.

Import Id.

Definition initialState (m: M) : option State_t :=
    find_State (fun s => NodeId_beq (Id "S0") s.(State_id)) m.(modelElements).

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
  List.In (TransitionElement t) (Model.modelElements m)
  /\ getTransition_source m t = Some s.
Proof.
  intro H.
  unfold State_outTransitions in H.
  apply OptionListUtils.filter_lift_in in H.
  destruct H as (? & ? & ? & ?).                   
  PropUtils.destruct_match H1 ; [ | discriminate H1]. 
  apply lem_State_t_beq_id in H1. subst s0.    
  destruct x ;[discriminate H0 | PropUtils.inj H0]. (* monadInv *) 
  auto.
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


Lemma search_in_left :
  forall m s1 a s2,
  search m s1 a = Some s2 ->
  List.In (StateElement s1) m.(Model.modelElements).
Proof.
  intros.
  destruct (search_inv _ _ _ _ H) as (?&?&?).
  destruct (State_acceptTransition_inv _ _ _ _ H0).
  destruct (State_out_transitions_inv _ _ _ H2).
  destruct (getTransition_source_inv _ _ _ H5).
  assumption.
Qed.

Lemma search_in_right :
  forall m s1 a s2,
  search m s1 a = Some s2 ->
  List.In (StateElement s2) m.(Model.modelElements).
Proof.
  intros.
  destruct (search_inv _ _ _ _ H) as (?&?&?).
  destruct (getTransition_target_inv _ _ _ H1).
  assumption.
Qed.


(** Some tests *)

Require Import transformations.Moore2MealyALT.tests.sampleMoore.

Compute execute InputModel ("A"::nil).      (* "b"  *)
Compute execute InputModel ("A"::"B"::nil). (* "bb" *)
Compute execute InputModel ("B"::nil).      (* None *)
Compute execute InputModel ("A"::"A"::nil). (* None *)



