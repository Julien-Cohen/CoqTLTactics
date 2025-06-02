From Stdlib 
  Require Import String EqNat List PeanoNat Lia FunctionalExtensionality.

From core 
  Require Import Semantics Syntax Model TransformationConfiguration Certification utils.Utils.

From core.modeling 
  Require Import ConcreteSyntax ModelingSemantics ModelingMetamodel ConcreteExpressions Parser.

From core.properties.monotonicity
  Require Import Moore2Mealy_monotonicity_elem_witness sampleMoore_monotonicity_elem.

(*************************************************************)
(** * Monotonicity of CoqTL  (element)                       *)
(** * Using operational semantics                            *)
(*************************************************************)

Definition SourceModel_elem_incl {tc: TransformationConfiguration}  (m1 m2: SourceModel) : Prop := 
  incl (modelElements m1) (modelElements m2). 

Definition TargetModel_elem_incl {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  incl (modelElements m1) (modelElements m2). 

Definition Monotonicity_elem {tc: TransformationConfiguration} 
   (tr: Transformation) :=
forall sm1 sm2,
    SourceModel_elem_incl sm1 sm2 ->
    TargetModel_elem_incl (execute tr sm1) (execute tr sm2).  

Lemma Moore2Mealy_non_mono_contrapos_elem:
  exists sm1 sm2 : SourceModel,
    SourceModel_elem_incl sm1 sm2 /\
      ~ TargetModel_elem_incl (execute Moore2Mealy sm1) (execute Moore2Mealy sm2).
Proof.
  exists Moore_m1.
  exists Moore_m2.
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

Lemma Moore2Mealy_non_mono_elem : ~ (Monotonicity_elem Moore2Mealy).
Proof.
  unfold Monotonicity_elem.
  intro.
  specialize Moore2Mealy_non_mono_contrapos_elem ; intro H2.
  crush.
Qed.

Lemma exists_non_mono_elem  :
    exists tr, ~ (Monotonicity_elem tr).
Proof.
  exists Moore2Mealy.
  apply Moore2Mealy_non_mono_elem.
Qed.

Theorem non_mono_elem  :
   ~ (forall tr, (Monotonicity_elem tr)).
Proof.
  intro.
  specialize (exists_non_mono_elem).
  intro.
  destruct H0.
  specialize (H x).
  contradiction.
Qed.