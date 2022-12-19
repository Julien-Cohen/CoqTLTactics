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

Ltac inj H := injection H ; clear H ; intros ; subst.


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


(** *** singleton rules and singleton transformations *)

(** We say an abstract rule is a singleton rule when it matches singletons. *)

Section A.

Variable tc : TransformationConfiguration.
Variable mtc : ModelingTransformationConfiguration tc.

Definition singleton_rule_a (r: Syntax.Rule (tc:=tc)) : Prop := 
      (forall m, r.(Syntax.r_guard) m nil = false) /\
        (forall m e1 e2 s, r.(Syntax.r_guard) m (e1 :: e2 :: s) = false).


Lemma singleton_nil_false : 
  forall r, 
    singleton_rule_a r ->
    forall m,
      Expressions.evalGuardExpr r m nil = false.
Proof.
  intros r A m.
  destruct r.
  simpl in *.
  destruct A as [A _]. simpl in A.
  apply A.
Qed.


Lemma singleton_two_false : 
  forall a, 
    singleton_rule_a a ->
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


(** We say a concrete rule is a singleton rule when it pattern is a list of size 1. *)
Definition singleton_rule_c (a:ConcreteRule (tc:=tc) (mtc:=mtc)) :=
  match a with 
  | (ConcreteSyntax.Build_ConcreteRule s [m] o o0 l) => True
  | _ => False
  end.

(** A concrete singleton rule gives an abstract singleton rule. *)


Lemma singleton_rule_parse : 
  forall a, 
    singleton_rule_c a ->
    singleton_rule_a (Parser.parseRule a).
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


(** We say an abstract transformation is singleton transformation when its rules are singleton rules. *)

Definition singleton_transformation_a (t:Syntax.Transformation) : Prop :=
  List.Forall singleton_rule_a t.(Syntax.rules).


(** We say a concrete transformation is a singleton rule when its rules are singleton rules. *) 

Definition singleton_transformation_c t := 
  match t with 
    ConcreteSyntax.transformation l =>
      Forall singleton_rule_c l
  end.

(** A concrete singleton transformation gives an abstract singleton transformation. *)

Lemma singleton_transformation_parse : 
  forall t,
    singleton_transformation_c t ->
    singleton_transformation_a (Parser.parse t).
Proof.
  intros t H ; destruct t.
  unfold singleton_transformation_c in H.
  unfold Parser.parse ; simpl.
  induction l ; simpl.
  { constructor. }
  { inversion_clear H.
    constructor. 
    { apply singleton_rule_parse ; assumption. }
    { apply IHl ; assumption. }
  }
Qed.

(** *** Properties on [instantiatePattern] for singleton transformations *)

Lemma instpat_nil : 
  forall t, 
    singleton_transformation_a t ->
    forall m,
      instantiatePattern t m nil = nil.
Proof.
  intro t ; destruct t ; simpl.
  unfold singleton_transformation_a ; simpl.
  unfold instantiatePattern ; simpl.
  unfold matchPattern ; simpl.
  induction rules ; intros A m ; inversion_clear A ; simpl ; [reflexivity | ].
  rewrite singleton_nil_false ; auto.
Qed.

Lemma instpat_two : 
  forall t, 
    singleton_transformation_a t ->
    forall m e1 e2 r,
      instantiatePattern t m (e1 :: e2 :: r) = nil.
Proof.
  intros t ; destruct t ; simpl.
  unfold singleton_transformation_a ; simpl.
  unfold instantiatePattern ; simpl.
  unfold matchPattern ; simpl.
  induction rules ; intros A m e1 e2 r; inversion_clear A ; simpl ; [reflexivity | ].
  rewrite singleton_two_false ; auto.
Qed.


Lemma instpat_singleton : 
  forall t, 
    singleton_transformation_a t ->
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

Import Model.

Lemma allModelElements_allTuples_back {tc:TransformationConfiguration} (e:tc.(SourceElementType)) (t:Syntax.Transformation (tc:=tc)) (cm:tc.(SourceModel)) : 
  In [e] (allTuples t cm) ->
  In e cm.(modelElements).
Proof.
  intro.
  apply incl_singleton.
  eapply Certification.allTuples_incl.
  exact H.
Qed.

Ltac in_singleton_allTuples :=
  match goal with 
    [ H : In [_] (allTuples _ _) |- _ ] =>
      apply allModelElements_allTuples_back in H
  end.

Lemma allModelElements_allTuples {tc:TransformationConfiguration} e t cm: 
  In e cm.(modelElements) ->
  0 < Syntax.arity t ->
  In [e] (allTuples t cm).
Proof. 
  intros.
  apply Certification.allTuples_incl_length.
   + apply incl_singleton. assumption.
   + compute. auto.
Qed.
