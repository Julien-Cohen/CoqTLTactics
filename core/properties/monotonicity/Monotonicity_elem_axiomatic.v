
Require Import String.
Require Import EqNat.
Require Import List.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.

Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.utils.Utils.




(*************************************************************)
(** * Monotonicity of CoqTL  (element)                       *)
(** * Using axiomatic semantics                              *)
(*************************************************************)


(* Definition SourceModel_elem_incl {tc: TransformationConfiguration}  (m1 m2: SourceModel) : Prop := 
  incl (modelElements m1) (modelElements m2). 

Definition TargetModel_elem_incl {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  incl (modelElements m1) (modelElements m2). 

Definition Monotonicity {tc: TransformationConfiguration} 
   (tr: Transformation) :=
forall sm1 sm2,
    SourceModel_elem_incl sm1 sm2 ->
    TargetModel_elem_incl (execute tr sm1) (execute tr sm2).  

Require Import core.properties.monotonicity.Moore2Mealy_monotonicity_witness.
Require Import core.properties.monotonicity.sampleMoore_monotonicity.

Lemma Moore2Mealy_non_mono_contrapos:
  exists sm1 sm2 : SourceModel,
    SourceModel_elem_incl sm1 sm2 /\
      ~ TargetModel_elem_incl (execute Moore2Mealy sm1) (execute Moore2Mealy sm2).
Proof.
  eexists Moore_m1.
  eexists Moore_m2.
  split.
  - unfold SourceModel_elem_incl.
    simpl.
    remember (Moore.State
                (Moore.Build_State_t (Id.Id "S0") "1")) as elem.
    unfold incl.
    intros.
    destruct H.
    crush.
    destruct H.
  - unfold TargetModel_elem_incl.
    simpl.
    crush.
    apply incl_l_nil in H.
    crush.
Qed.

Theorem Moore2Mealy_non_mono  :
    exists tr, Monotonicity tr -> False.
Proof.
  eexists Moore2Mealy.
  unfold Monotonicity.
  intro mono.
  specialize (Moore2Mealy_non_mono_contrapos) as mono_contrapos.
  crush.
Qed. *)

Require AxiomaticSemantics.

Definition Monotonicity_elem {tc: TransformationConfiguration} 
   (tr: Transformation) :=
forall tr sm1 sm2 rm1 rm2,
  AxiomaticSemantics.is_result tr sm1 rm1 ->
  AxiomaticSemantics.is_result tr sm2 rm2 ->
    incl sm1.(modelElements) sm2.(modelElements) ->
    incl rm1.(modelElements) rm2.(modelElements).

Require Import core.properties.monotonicity.Moore2Mealy_monotonicity_elem_witness.
Require Import core.properties.monotonicity.sampleMoore_monotonicity_elem.

Lemma Moore2Mealy_non_mono_elem_witness:
    exists sm1 sm2 rm1 rm2,
    AxiomaticSemantics.is_result Moore2Mealy sm1 rm1 /\
    AxiomaticSemantics.is_result Moore2Mealy sm2 rm2 /\
      incl sm1.(modelElements) sm2.(modelElements) /\
      ~ (incl rm1.(modelElements) rm2.(modelElements)).
Proof.
  eexists Moore_m1.
  eexists Moore_m2.
  eexists (execute Moore2Mealy Moore_m1).
  eexists (execute Moore2Mealy Moore_m2).
  split.
  - apply AxiomaticSemantics.prop13.
  - split. apply AxiomaticSemantics.prop13.
    --  split. 
        unfold incl.
        simpl.
        intros.
        destruct H. right. right. left. exact H.
        inversion H.
  simpl.
  unfold not.
  intro.
  apply incl_l_nil in H.
  inversion H.
Qed.

Theorem Moore2Mealy_non_mono  :
    exists tr, Monotonicity_elem tr -> False.
Proof.
  eexists Moore2Mealy.
  unfold Monotonicity_elem.
  intro.
  specialize (Moore2Mealy_non_mono_elem_witness) as witness.
  destruct witness.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H2.
  specialize (H Moore2Mealy x x0 x1 x2 H0 H1 H2).
  contradiction.
Qed.  
  