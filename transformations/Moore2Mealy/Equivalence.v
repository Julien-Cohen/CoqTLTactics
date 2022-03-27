Require Import String.
Require Import Moore.
Require Import MooreSemantics.
Require Import Mealy.
Require Import MealySemantics.
Require Import Moore2Mealy.
Require Import core.Syntax.
Require Import List.
Require Import core.Engine.
Require Import core.modeling.ModelingEngine.
Require Import core.Semantics.
Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Certification.
Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.
Require Import core.SyntaxCertification.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.
Require Import core.TraceLink.
Require Import Coq.Logic.Eqdep_dec.


Scheme Equality for list.

Definition toOb s := toModelElement StateClass s.
Definition toOb' := toModelElement Mealy.StateClass.

(* put in metamodels, auto gen *)
Lemma mealy_state_convert: 
forall x s,
MealyMetamodel_toClass StateClass x = return s ->
toModelElement StateClass s = x.
Proof.
intros.
unfold MealyMetamodel_toObject .
destruct x.
simpl in H.
destruct (MealyMetamodel_eqEClass_dec mecl_arg StateClass); crush.
Qed.

Lemma Moore2Mealy_executeFromState_eq :
forall (m : MooreModel) (i: list string)
(q0: Moore.State) (q0': State) tl, 
In tl (trace Moore2Mealy m) ->
MooreMetamodel_toStates (TraceLink_getSourcePattern tl) = [q0] ->
MealyMetamodel_toStates [(TraceLink_getTargetElement tl)] = [q0'] -> 
MooreSemantics.executeFromState m q0 i =
executeFromState (execute Moore2Mealy m) q0' i.
Proof.
intros m inputs.
induction inputs.
- intros. simpl. auto.
- intros q0 q0' trace rel q0_id q0'_id.
  (* main induction step *)
  (* fold mr_execute just once *)
  unfold MooreSemantics.executeFromState; fold MooreSemantics.executeFromState.
  destruct (MooreSemantics.State_acceptTransition q0 m a) eqn: mr_q0_atr.
  * destruct (Moore.Transition_getTarget t m) eqn: mr_atr_trg.
    ** unfold executeFromState; fold executeFromState.
       destruct (State_acceptTransition q0' (execute Moore2Mealy m) a) eqn: ml_q0'_atr.
       *** destruct (Transition_getTarget t0 (execute Moore2Mealy m)) eqn: ml_atr_trg.
           **** (* assert State_getOutput s = Transition_getOutput t0 *)
                (* apply induction step IHinputs *)
                admit.
           **** (* contradiction *) admit.
        *** (* contradiction *) admit.
    ** unfold executeFromState; fold executeFromState. 
       destruct (State_acceptTransition q0' (execute Moore2Mealy m) a) eqn: ml_q0'_atr.
       *** destruct (Transition_getTarget t0 (execute Moore2Mealy m)) eqn: ml_atr_trg.
           **** (* contradiction *) admit.
           **** auto.
       *** (* contradiction mr_q0_atr, ml_qo'_atr *) auto.
  * unfold executeFromState; fold executeFromState.
    destruct (State_acceptTransition q0' (execute Moore2Mealy m) a) eqn: ml_q0'_atr.
    ** (* contradiction *) admit.
    ** auto.

Admitted.


Lemma Moore2Mealy_initial_state_eq:
forall (m : MooreModel), 
initialState (execute Moore2Mealy m) = None ->
MooreSemantics.initialState m = None.
Proof. 
Admitted.

Lemma Moore2Mealy_initial_state_eq:
forall (m : MooreModel) s, 
initialState (execute Moore2Mealy m) = Some s ->
MooreSemantics.initialState m = None -> False.
Proof. 
intros m s q0_tr q0.
assert (In (toOb' s) (allModelElements (execute Moore2Mealy m))).
      { unfold initialState in q0_tr.  unfold MealyMetamodel_allStates in q0_tr.
      apply find_some in q0_tr. 
      destruct q0_tr.
      unfold MealyMetamodel_toStates in H.
      apply optionList2List_In in H.
      apply in_map_iff in H.
      do 2 destruct H.
      unfold toOb'.
      assert ((toModelElement StateClass s) = x). apply mealy_state_convert. auto.
      rewrite H2.
      auto.
      }

      apply in_flat_map in H as [sp H].
      destruct H.
      apply in_flat_map in H0 as [r H0].
      destruct H0.

      destruct sp.
      * simpl in H0. crush.
      * destruct sp.
        (* sp = n::nil *)
        ** destruct s0.
          destruct mocl_arg eqn: clz.
          - simpl in H0.
            destruct H0.
            -- rewrite <- H0 in H1. simpl in H1. 
              destruct H1. 
                unfold initialState in q0_tr.
                apply find_some in q0_tr.
                unfold toOb' in H1.
                assert (MealyMetamodel_toObject StateClass (BuildState (Moore.State_getName m0)) =
                MealyMetamodel_toObject StateClass s). crush.
                apply Mealy_invert in H2.
                destruct q0_tr.
                apply eqb_eq in H4.
                rewrite <- H2 in H4. simpl in H4.
                unfold MooreSemantics.initialState.
                apply find_none with (x:=m0) in q0.
                apply eqb_neq in q0.
                --- contradiction.
                --- unfold MooreMetamodel_allStates. 
                unfold MooreMetamodel_toStates.
                (* unfold al
                lTuples in H. *)
                apply tuples_up_to_n_incl in H.
                unfold incl in H.
                apply optionList2List_In_inv.
                apply in_map_iff.
                exists (Build_MooreMetamodel_Object Moore.StateClass m0).
                split.
                simpl. auto.
                specialize (H (Build_MooreMetamodel_Object Moore.StateClass m0)).
                simpl in H.
                crush.
                --- inversion H1.
            -- crush.
          -  simpl in H0.
              destruct H0.
              -- rewrite <- H0 in H1.
                  simpl in H1.
                  destruct H1.
                  --- unfold toOb' in H1. inversion H1.
                  --- inversion H1.
              -- inversion H0.
        ** (* sp = n::mm::nil *)
           destruct s0.
           destruct mocl_arg eqn: clz; simpl in H0; inversion H0.
Qed.

Theorem Moore2Mealy_equivalence :
    forall (m : MooreModel) (i: list string), 
        Moore_execute m i = Mealy_execute (execute Moore2Mealy m) i.
Proof.
intros.
unfold Moore_execute, Mealy_execute.
destruct (MooreSemantics.initialState m) eqn: q0.
+ destruct (initialState (execute Moore2Mealy m)) eqn: q0_tr.
  ++ (* apply Moore2Mealy_executeFromState_eq *)
     admit.
  ++ (* contradiction, apply Moore2Mealy_initial_state_eq *) admit.
+ destruct (initialState (execute Moore2Mealy m)) eqn: q0_tr.
  ++ specialize (Moore2Mealy_initial_state_eq m s q0_tr q0). intro. inversion H.  
  ++ auto.
Admitted.

