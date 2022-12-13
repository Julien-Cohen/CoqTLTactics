Require Import core.Semantics.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

(** General purpose tactics *)

Ltac destruct_match :=
  match goal with 
     [ |- context[match ?P with | _ => _ end]] => destruct P end. 

(* To replace the [inversion] tactics on equalities on a dependant type constructor. *)
Ltac dep_inversion H := 
  let H':= fresh H in
  inversion H as [H'] ; apply Eqdep.EqdepTheory.inj_pair2 in H'.


(** Tactics to deal with boolean equality on generated types. *)

(** (When we have generated a boolean equality function [eqb] on a type [T], [beq_eq_tac] proves that [forall (a:T) (b:T), eqb a b = true => a = b]. *)

Ltac basetype_eqb_eq_tac :=
  match goal with 
  | [ H : Nat.eqb    _ _ = true |- _ ] => apply EqNat.beq_nat_true in H ; subst 
  | [ H : Bool.eqb   _ _ = true |- _ ] => apply Bool.eqb_prop      in H ; subst 
  | [ H : beq_string _ _ = true |- _ ] => apply lem_beq_string_eq2 in H ; subst 
end.

Import Bool. (* for "&&" notation *)

Ltac composedtype_eqb_eq_tac :=
  match goal  with [ H : ?f ?a ?b = true |- _ ]  => unfold f in H  ; (* unfold the boolean equality function *)
  destruct a , b ; simpl in H end ;  
  repeat ( (* destruct conjunctions *)
      match goal with   
        [ H : ?e && _ = true |- _ ] => apply Bool.andb_true_iff in H ; destruct H  
      end).

Notation beq_is_eq f := (forall a b, f a b = true -> a = b).

Lemma lem_list_beq_eq {T} : 
  forall (f:T->T->bool),
    beq_is_eq f ->
    beq_is_eq (core.Model.list_beq f).
Proof.
  intros f C.
  induction a ; intro b ; destruct b ; simpl ; first [ discriminate | reflexivity | idtac ] ; [].
  intro E ; apply Bool.andb_true_iff in E ; destruct E.  
  f_equal ; [ apply C | apply IHa ] ; auto.
Qed.


Create HintDb beq_eq_database.
(* This HintDb is used by the [auto with] tactics below to uses lemmas on intermediate types that will be generated (and registered in the DB) *)

Ltac list_eqb_eq_tac :=
  match goal with
  | [ H : core.Model.list_beq _ _ _ = true |- _] => apply lem_list_beq_eq in H ; [ subst | solve[auto with beq_eq_database]]
  end.


Ltac beq_eq_tac :=
  let a := fresh "a" in
  let b := fresh "b" in
  let E := fresh "E" in
  intro a ; intro b ; intro E ;
  repeat first [ 
      basetype_eqb_eq_tac 
    | composedtype_eqb_eq_tac  
    | list_eqb_eq_tac
    ] ; 
  reflexivity 
.


(** *** One-to-one rules and transformations *)

(** We say a rule is one-to-one rule when it matches singletons. *)

Section A.

Variable tc : TransformationConfiguration.
Variable mtc : ModelingTransformationConfiguration tc.

Definition one_to_one_rule (r: Syntax.Rule (tc:=tc)) : Prop := 
      (forall m, r.(Syntax.r_guard) m nil = false) /\
        (forall m e1 e2 s, r.(Syntax.r_guard) m (e1 :: e2 :: s) = false).


Lemma one_to_one_nil_false : 
  forall a, 
    one_to_one_rule a ->
    forall m,
      Expressions.evalGuardExpr a m nil = false.
Proof.
  intros a A m.
  destruct a.
  simpl in *.
  destruct A as [A _]. simpl in A.
  apply A.
Qed.


Lemma one_to_one_two_false : 
  forall a, 
    one_to_one_rule a ->
    forall m e1 e2 r,
      Expressions.evalGuardExpr a m (e1::e2::r) = false.
Proof.
  intros a A m e1 e2 r.
  destruct a.
  simpl in *.
  destruct A as [_ A] ; simpl in A.
  apply A.
Qed.

(** *** Singleton-pattern rules and transformations *)


(** We say a rule has a singleton-pattern when it pattern is a list of size 1. *)
Definition singleton_pattern_rule (a:ConcreteRule (tc:=tc) (mtc:=mtc)) :=
  match a with 
  | (ConcreteSyntax.Build_ConcreteRule s [m] o o0 l) => True
  | _ => False
  end.

(** A singleton-pattern rule is also a one-to-one rule. *)


Lemma one_to_one_rule_parse : 
  forall a, 
    singleton_pattern_rule a ->
    one_to_one_rule (Parser.parseRule a).
Proof.
  intros a H.
  destruct a ; simpl in H.
  destruct r_InKinds ; [ contradiction | ].
  destruct r_InKinds ; [ | contradiction ].
  clear H.
  simpl.
  split ; intro m ; [ | ].
  { simpl. destruct r_guard ; reflexivity. }
  {
    intros e1 e2 r.
    simpl.
    destruct r_guard ; simpl.
    { 
      unfold ConcreteExpressions.makeGuard. simpl.
      destruct (toEData e e1) ; reflexivity.
    }
    { unfold makeEmptyGuard.  
      unfold wrap'.
      unfold wrap.
      destruct (toEData e e1) ; reflexivity.
    }
  }
Qed.


(** We say a transformation is one-to-one when its rules are one-to-one. *)

Definition one_to_one_transformation (t:Syntax.Transformation) : Prop :=
  List.Forall one_to_one_rule t.(Syntax.rules).


(** We say a transformation has singleton-patterns when its rules have singleton-patterns. *) 

Definition singleton_pattern_transformation t := 
  match t with 
    ConcreteSyntax.transformation l =>
      Forall singleton_pattern_rule l
  end.

(** A singleton-pattern transformation is also a one-to-one transformation. *)

Lemma one_to_one_transformation_parse : 
  forall t,
    singleton_pattern_transformation t ->
    one_to_one_transformation (Parser.parse t).
Proof.
  intros t H ; destruct t.
  unfold singleton_pattern_transformation in H.
  unfold Parser.parse ; simpl.
  induction l ; simpl.
  { constructor. }
  { inversion_clear H.
    constructor. 
    { apply one_to_one_rule_parse ; assumption. }
    { apply IHl ; assumption. }
  }
Qed.

(** *** Properties on [instantiatePattern] for one-to-one transformations *)

Lemma instpat_nil : 
  forall t, 
    one_to_one_transformation t ->
    forall m,
      instantiatePattern t m nil = nil.
Proof.
  intro t ; destruct t ; simpl.
  unfold one_to_one_transformation ; simpl.
  unfold instantiatePattern ; simpl.
  unfold matchPattern ; simpl.
  induction rules ; intros A m ; inversion_clear A ; simpl ; [reflexivity | ].
  rewrite one_to_one_nil_false ; auto.
Qed.

Lemma instpat_two : 
  forall t, 
    one_to_one_transformation t ->
    forall m e1 e2 r,
      instantiatePattern t m (e1 :: e2 :: r) = nil.
Proof.
  intros t ; destruct t ; simpl.
  unfold one_to_one_transformation ; simpl.
  unfold instantiatePattern ; simpl.
  unfold matchPattern ; simpl.
  induction rules ; intros A m e1 e2 r; inversion_clear A ; simpl ; [reflexivity | ].
  rewrite one_to_one_two_false ; auto.
Qed.


Lemma instpat_singleton : 
  forall t, 
    one_to_one_transformation t ->
    forall m a,
      instantiatePattern t m a <> nil ->
      exists b, a = b::nil.
Proof.
  intros t A m a B.
  destruct a ; [ exfalso | ].
  { contradict B ; apply instpat_nil ; assumption. }
  {
    destruct a ; eauto ; [].    
    exfalso.
    contradict B; apply instpat_two ; assumption. 
  }
Qed.


End A.

Require Certification.

(** Tactics to transform an hypothesis H : In [e] (allTuples _ cm)
    into H: In (e) (modelElements cm)
*)

Ltac in_singleton_allTuples :=
  match goal with 
    [ H : In [_] (allTuples _ _) |- _ ] =>
      apply Certification.allTuples_incl in H ;
      apply incl_singleton in H
  end.
