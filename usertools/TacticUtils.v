Require Import core.Semantics.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Require Certification.

Import Metamodel Model.


#[global]
Hint Unfold 
  Semantics.traceTrOnPiece 
  Semantics.traceRuleOnPiece 
  Semantics.traceIterationOnPiece 
  Semantics.traceElementOnPiece 
  Semantics.produced_elements 
  : trace.

#[global]
Hint Unfold 
  Semantics.execute 
  Semantics.compute_trace 
  Semantics.produced_elements : semantics.


(** *** Utilities on help the resolution of In/lists *)

(** When we know which rule is the one we search, the following tactics help us to say it. 

In particular in the case we have an existential variable in the goal, as in [In ?r (Syntax.rules Class2Relational)]
(after use of [in_compute_trace_inv]).

*)


(** First element in list (1 lemma, 2 tactics) *)
Lemma In_1 {A} :
      forall (e:A) s,
      (exists r, s = e :: r) -> In e s.
Proof.
  intros e s (r&E) ; subst s. 
  apply in_eq.
Qed.

Ltac first_in_list :=
  match goal with 
    [ |- In _ _ ] =>
      apply In_1 ; eexists ; reflexivity
  end.

Ltac first_rule :=
  match goal with 
    [ |- In _ (Syntax.rules _)] =>
      first_in_list
  end.


(** Second element in list (1 lemma, 2 tactics) *)
Lemma In_2 {A} :
      forall (e:A) s,
      (exists a r, s = a :: e :: r) -> In e s.
Proof.
  intros e s (a&r&E) ; subst s. 
  apply in_cons. apply in_eq.
Qed.

Ltac second_in_list :=
  match goal with 
    [ |- In _ _ ] =>
      apply In_2 ; eexists ; eexists ; reflexivity
  end.

Ltac second_rule :=
  match goal with 
    [ |- In _ (Syntax.rules _)] =>
      second_in_list
  end.


(** switch/case on positions in lists *)

Ltac rule_number n := 
  match n with 
    1 => first_rule 
  | 2 => second_rule 
end.

Ltac pattern_number n :=
  match n with 
    1 => first_in_list 
  | 2 => second_in_list 
  end.


(** ** Utilities for tactics that need backtracking *)

Ltac multi_eassumption :=
    multimatch goal with
      | [ H : In _ (modelElements _) |- _ ] => exact H 
    end.

Ltac incl_singleton :=
  apply ListUtils.incl_singleton ; 
  multimatch goal with
    [ H : List.In _ _ |- _ ] => exact H 
                            
    (* multimatch is important here because it allows backtracking, as opposed to eassumption. Here, if there are two hypothesis in the context that allow to solve the goal, because of evar in the goal, if the the selected hypothesis instanciates the evar so that the following tactics fail, it will backtrack and select another one.  This situation can be explored in the proof of Moore2MEaly/theorems/Links/source_link_fw (use move to switch the order of hypothesis) *)

  end.


(* When a guard is applied to an input piece that does not match the expected type, evaluation of the guard will lead to false = true.
   This tacic detects this situation and fails when it occurs. Such a failure should be used to trigger a backtrack. *)
Ltac fail_on_type_mismatch :=
  tryif 
    compute ;
    match goal with 
      [ |- false = true]  => idtac 
    end 
  then fail 
  else idtac.

Ltac fail_on_False :=
  tryif 
    simpl ; 
    match goal with 
      [ |- False] => idtac 
    end 
  then fail 
  else idtac.
