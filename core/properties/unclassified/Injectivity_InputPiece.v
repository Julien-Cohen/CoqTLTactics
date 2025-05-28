From Stdlib Require Import String.
From Stdlib Require Import EqNat.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.

Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.
Require Import core.AxiomaticSemantics.

Require Import transformations.Moore2Mealy.Moore.
Require Import core.properties.injectivity.Moore2Mealy_injectivity_inputpiece_witness.
Require Import core.properties.injectivity.sampleMoore_injectivity_inputpiece.

(*************************************************************)
(** * Injectivity of Stdlib.L (InputPiece)                      *)
(** * Using Axiomatic semantics                              *)
(*************************************************************)

(** M.T. this does not hold if two different source patterns generate target patterns with a non-empty intersection*)
(* Theorem Injectivity_elem :
forall (tr: Transformation) (sm : SourceModel) (te : TargetElementType) (sp1 sp2: InputPiece),
  AxiomaticSemantics.is_produced_element tr sm te ->
    isTuple sm sp1 -> 
    isTuple sm sp2 -> 
      TranOnPiece_rel tr sm sp1 te -> 
      TranOnPiece_rel tr sm sp2 te -> 
        sp1 = sp2.
Proof.
Abort. *)

(** FIXME we could consider to move this into AxiomaticSemantics *)
Inductive TranOnPiece_rel {tc: TransformationConfiguration} (tr: Transformation) (sm : SourceModel) (sp: InputPiece) (te: TargetElementType) : Prop :=
  | TranOnPiece_rel_def : forall tl, 
  traceTrOnPiece_rel tr sm sp tl ->
    tl.(TraceLink.produced) = te ->
        TranOnPiece_rel tr sm sp te.

(** NOTES this is to link to operational semantic *)
Lemma prop14 : forall {tc: TransformationConfiguration} tr sm sp te,
TranOnPiece_rel tr sm sp te <-> (exists tlk, traceTrOnPiece_rel tr sm sp tlk /\ tlk.(TraceLink.produced) = te).
Proof.
  intros.
  split.
  - intro.
    destruct H.
    exists tl. split; assumption.
  - intro.
    destruct H.
    remember (TranOnPiece_rel_def tr sm sp te x) as def.
    apply def; destruct H; assumption.
Qed.

Definition Injectivity_inputpiece_axiomatic {tc: TransformationConfiguration} (tr: Transformation) :=
forall (sm : SourceModel) (te : TargetElementType) (sp1 sp2: InputPiece),
  AxiomaticSemantics.is_produced_element tr sm te ->
    isTuple sm sp1 -> 
    isTuple sm sp2 -> 
      TranOnPiece_rel tr sm sp1 te -> 
      TranOnPiece_rel tr sm sp2 te -> 
        sp1 = sp2.

Lemma Moore2Mealy_non_inj_elem_contrapos_axiomatic:
exists (sm : SourceModel) (te : TargetElementType)  (sp1 sp2: InputPiece),
  AxiomaticSemantics.is_produced_element Moore2Mealy sm te /\
  isTuple sm sp1 /\
  isTuple sm sp2 /\ 
  TranOnPiece_rel Moore2Mealy sm sp1 te /\ 
  TranOnPiece_rel Moore2Mealy sm sp2 te /\ 
  sp1 <> sp2.
Proof.
  exists Moore_m1.
  exists (Mealy.State {| Mealy.State_id := Id.Id "S0" |}).
  exists ((State (Build_State_t (Id.Id "S0") "1"))::nil).
  exists ((State (Build_State_t (Id.Id "S0") "0"))::nil).
  repeat split.
  - apply prop11. simpl. left. reflexivity.
  - apply prop1 with (tr:=Moore2Mealy). simpl. left. reflexivity.
  - apply prop1 with (tr:=Moore2Mealy). simpl. right. left. reflexivity.
  - apply prop14.
    eexists.
    split.
    apply prop6.
    simpl.
    left.
    reflexivity.
    simpl. reflexivity.
  - (* FIXME same as last goal, we could refactor here. *)
    apply prop14.
    eexists.
    split.
    apply prop6.
    simpl.
    left.
    reflexivity.
    simpl. reflexivity.
  - crush.
Qed.

Lemma Moore2Mealy_non_injective_inputpiece : ~ (Injectivity_inputpiece_axiomatic Moore2Mealy).
Proof.
  unfold Injectivity_inputpiece_axiomatic.
  intro inj.
  specialize (Moore2Mealy_non_inj_elem_contrapos_axiomatic) as inj_contrapos.
  (* FIXME contradiction is not directly crushed. we could consider refactor Moore2Mealy_non_inj_elem_contrapos_axiomatic.*)
  crush.
  specialize (inj x x0 x1 x2 H0 H H1 H2 H3).
  contradiction.
Qed.

Lemma exists_non_injective_inputpiece :
  exists tr, ~ (Injectivity_inputpiece_axiomatic tr).
Proof.
  exists Moore2Mealy.
  apply Moore2Mealy_non_injective_inputpiece.
Qed.

Theorem non_injective_inputpiece  :
   ~ (forall tr, (Injectivity_inputpiece_axiomatic tr)).
Proof.
  intro.
  specialize (exists_non_injective_inputpiece).
  intro.
  destruct H0.
  specialize (H x).
  contradiction.
Qed.

(*************************************************************)
(** * Injectivity of Stdlib.L (InputPiece)                      *)
(** * FIXME Another Case                                     *)
(*************************************************************)

Definition is_produced_elems_eq tr sm sp1 sp2 : Prop :=
  (forall te, TranOnPiece_rel tr sm sp1 te <-> TranOnPiece_rel tr sm sp2 te).

(** M.T. this holds if two different source patterns generate target patterns with a non-empty intersection*)
Theorem Injectivity_elem' :
forall (tr: Transformation) (sm : SourceModel) (sp1 sp2: InputPiece),
  isTuple sm sp1 -> 
  isTuple sm sp2 -> 
  is_produced_elems_eq tr sm sp1 sp2 ->
    (* (produced_elements (traceTrOnPiece tr sm sp1)) = (produced_elements (traceTrOnPiece tr sm sp2)) ->  *)
      sp1 = sp2.
Proof.
Abort.