Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
From Stdlib Require Import String.
From Stdlib Require Import EqNat.
From Stdlib Require Import List.
Require Import core.utils.Utils.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.

Require AxiomaticSemantics.

(*************************************************************)
(** * Additivity in Rule context (Elem)                      *)
(** * Using Axiomatic semantics                              *)
(*************************************************************)

Definition Transformation_incl_rules {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (t1.(arity) = t2.(arity)) /\ 
  forall r: Rule, In r t1.(rules) -> In r t2.(rules).

Definition Rule_Additivity_Elem {tc: TransformationConfiguration} :=
forall (t1 t2: Transformation) (sm: SourceModel),
    (Transformation_incl_rules t1 t2 -> 
        incl (execute t1 sm).(modelElements) (execute t2 sm).(modelElements)). 

Lemma additivity_rules_general_axiomatic :
forall {tc: TransformationConfiguration} (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_rules t1 t2 -> 
  forall rm1 rm2,
  AxiomaticSemantics.is_result t1 sm rm1 ->
  AxiomaticSemantics.is_result t2 sm rm2 ->
    incl  rm1.(modelElements)  rm2.(modelElements)).
Proof.
  unfold AxiomaticSemantics.is_result.
  intros tc t1 t2 sm H rm1 rm2 (H1 & _) (H2 & _).
  unfold incl.
  intros e H_IN.
  specialize (H1 e).
  specialize (H2 e).
  apply H2.
  apply H1 in H_IN.
  clear H1 H2. 
  
  inversion_clear H_IN.
  
  econstructor. 
  (* Show Existentials. *)
  instantiate (2:=a).
  instantiate (1:=c).

  unfold Transformation_incl_rules in H.
  destruct H as (H1 & H2).

  inversion_clear H0.
  econstructor.
  instantiate (1:=sp).

  3:{ congruence. }
  
  2:{ assumption. }

  inversion_clear H.
  econstructor.
  instantiate (1:=r).
  
  assumption.  
  inversion_clear H5.
  constructor ; auto.
 
Qed.

Theorem forall_Additivity_Rules_Elem {tc: TransformationConfiguration} : Rule_Additivity_Elem.
Proof.
  unfold Rule_Additivity_Elem.
  intros. 
  apply additivity_rules_general_axiomatic with (t1:=t1) (t2:=t2) (sm:=sm) ; [ assumption | | ].
  + apply AxiomaticSemantics.prop13.
  + apply AxiomaticSemantics.prop13.
Qed.