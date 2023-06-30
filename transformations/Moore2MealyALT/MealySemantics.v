Require Import String.
Require Import List.

Require Import transformations.Moore2MealyALT.Mealy.
Require Import core.Model.
Require Import core.utils.Utils.

Import Id.

Definition initialState (m: M) : option State_t :=
    find_lift (get_E_data State_K) (fun s => NodeId_beq (Id "S0") s.(State_id)) m.(modelElements).

Definition State_outTransitions (m: M) (s: State_t) : list Transition_t :=
    filter_lift 
      (get_E_data Transition_K) 
      (fun t => 
         match (getTransition_source m t) with
         | Some s' => State_t_beq s s'
         | None => false
         end)
      m.(Model.modelElements).

Definition State_acceptTransition (m: M) (s: State_t) (i: string) : option Transition_t :=
    find (fun t => eqb i t.(Transition_input)) (State_outTransitions m s).

Definition search (m: M) (current: State_t) i :=
  match State_acceptTransition m current i with
  | None => None
  | Some t => match getTransition_target m t
              with
              | Some s => Some (t, s)
              | None => None (* impossible when models are well formed *)
              end
  end.

Fixpoint executeFromState (m: M) (current: State_t) (remainingInput: list string) : option (list string) :=
  match remainingInput with 
   | i :: inputs => 
       match search m current i with
        | None => None 
        | Some (t, s) =>  
            match executeFromState m s inputs with
            | Some r => Some (t.(Transition_output) :: r)
            | None => None
            end
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

(** Some tactics. *)
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
  destruct x ; [discriminate H0 | PropUtils.inj H0]. (* monadInv *) 
  auto.
Qed.



Lemma in_State_outTransitions (m:Mealy.M) s t :
  List.In (TransitionElement t) (Model.modelElements m) ->
  getTransition_source m t = Some s ->
  List.In t (State_outTransitions m s).
Proof.
  intros.
  unfold State_outTransitions.
  apply OptionListUtils.filter_lift_in.
  exists (TransitionElement t).
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
  forall m s i t r,
    search m s i = Some (t,r) -> 
    State_acceptTransition m s i = Some t /\
      getTransition_target m t = Some r.
Proof.
  unfold search ; intros.
  OptionUtils.monadInv H.
  OptionUtils.monadInv H.
  eauto.
Qed.

Lemma execute_in :
  forall m i s r,
    i <> nil ->
    executeFromState m s i = Some r ->
    List.In (StateElement s) m.(Model.modelElements).
Proof.    
  intros.

  destruct i.
  { contradiction. }
  { 
    simpl in H0.
    PropUtils.destruct_match H0 ; [ | discriminate].
    destruct p.
    clear H0.
    destruct (search_inv _ _ _ _ _ Heqo).

    destruct (State_acceptTransition_inv _ _ _ _ H0).
    destruct (State_out_transitions_inv _ _ _ H2).
    destruct (getTransition_source_inv _ _ _ H5).
    assumption.
  }
Qed.    


(** Some tests *)

Require Import transformations.Moore2MealyALT.tests.sampleMoore.
Require        core.Semantics.
Require Import transformations.Moore2MealyALT.Moore2Mealy.

Definition MealyTest := Semantics.execute Moore2Mealy InputModel.

Compute execute MealyTest ("A"::nil).      (* "b"  *)
Compute execute MealyTest ("A"::"B"::nil). (* "bb" *)
Compute execute MealyTest ("B"::nil).      (* None *)
Compute execute MealyTest ("A"::"A"::nil). (* None *)




