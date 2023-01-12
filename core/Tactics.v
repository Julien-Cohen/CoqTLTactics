Require Import core.Semantics.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

(** * General purpose tactics *)

Ltac destruct_match :=
  match goal with 
     [ |- context[match ?P with | _ => _ end]] => destruct P 
  end. 

Ltac destruct_if_hyp :=
  let E := fresh "E" in
 match goal with
        [ H : context[if ?B then _ else _] |- _ ] => destruct B eqn:E 
 end.

(* To replace the [inversion] tactics on equalities on a dependant type constructor. *)
Ltac dep_inversion H := 
  let H':= fresh H in
  inversion H as [H'] ; apply Eqdep.EqdepTheory.inj_pair2 in H'.

Ltac inj H := injection H ; clear H ; intros ; subst.

Ltac monadInv H :=
  let N := fresh "E" in

  match type of H with 
    _ <- ?E ; Some _ = Some _ => 
      destruct E eqn:N ;
      [ Tactics.inj H | discriminate H ] ; 
      let N2 := fresh H in
      rename N into N2

 | _ <- ?E ; _ = Some _ => 
      destruct E eqn:N ;
      [  | discriminate H ]
   end.
  
Ltac duplicate H1 H2 := remember H1 as H2 eqn:TMP ; clear TMP.


(** * Tactics to deal with boolean equality on generated types. *)

(** (When we have generated a boolean equality function [eqb] on a type [T], [beq_eq_tac] proves that [forall (a:T) (b:T), eqb a b = true => a = b]. *)

Ltac basetype_eqb_eq_tac :=
  match goal with 
  | [ H : Nat.eqb    _ _ = true |- _ ] => apply EqNat.beq_nat_true in H ; subst 
  | [ H : Bool.eqb   _ _ = true |- _ ] => apply Bool.eqb_prop      in H ; subst 
  | [ H : beq_string _ _ = true |- _ ] => apply lem_beq_string_eq2 in H ; subst 
end.


Ltac composedtype_eqb_eq_tac :=
  match goal  with [ H : ?f ?a ?b = true |- _ ]  => unfold f in H  ; (* unfold the boolean equality function *)
  destruct a , b ; simpl in H end ;  
  destruct_conjunctions
.

Notation beq_is_eq f := (forall a b, f a b = true -> a = b).

Lemma lem_list_beq_eq {T} : 
  forall (f:T->T->bool),
    beq_is_eq f ->
    beq_is_eq (core.utils.ListUtils.list_beq f).
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
  | [ H : core.utils.ListUtils.list_beq _ _ _ = true |- _] => apply lem_list_beq_eq in H ; [ subst | solve[auto with beq_eq_database]]
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


(** * Singleton rules and singleton transformations *)

(** *** Abstract rules *)

(** We say an abstract rule is a singleton rule when it matches only singletons. *)

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

(** *** Concrete rule *)

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

(** *** Transformations (abstract and concrete *)

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

(** ** Properties on [instantiatePattern] for singleton transformations *)

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
  forall t m a , 
      instantiatePattern t m a <> nil ->
      singleton_transformation_a t ->
      exists b, a = b::nil.
Proof.
  intros t m a H1 H2.
  destruct a ; [ exfalso | ].
  { contradict H1 ; apply instpat_nil ; assumption. }
  {
    destruct a ; eauto ; [].    
    exfalso.
    contradict H1; apply instpat_two ; assumption. 
  }
Qed.


End A.

Require Certification.

(** Tactics to transform an hypothesis H : In [e] (allTuples _ cm)
    into H: In (e) (modelElements cm)
*)

Import Model.

Lemma allModelElements_allTuples_back {tc:TransformationConfiguration} (t:Syntax.Transformation (tc:=tc)) (e:tc.(SourceElementType))  (cm:tc.(SourceModel)) : 
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
    [ H : In [_] (allTuples ?T _) |- _ ] =>
      apply allModelElements_allTuples_back with (t:=T) in H
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



(** Tactics to make appear that a sucessfully matched pattern is a singleton. The property that the given transformation is a single_transformation must be registered in the [singleton_rules] hintbase.*) 

Ltac show_singleton :=
  let TMP1 := fresh "N" in
  let TMP2 := fresh "TMP2" in
  let TMP3 := fresh "TMP3" in
  let E := fresh "e" in
  match goal with 
    [H:In ?B (instantiatePattern _ ?M ?A) |- _ ] =>
  
      specialize (in_not_nil B (instantiatePattern _ M A) H) ;
      intro TMP1 ; 
      specialize (instpat_singleton _ _ _ _ TMP1) ;
      intro TMP3 ; 
      destruct TMP3 as [ E TMP2] ; 
      [ solve [auto with singleton_rules]
      | subst A (* This [subst] ensures that if A is not a variable, this tactics fails. *) ]
       
  end.




(** ** Destructors *)

Ltac destruct_execute :=
  let H2 := fresh "IN_E" in
  let e := fresh "sp" in
  match goal with 

    [ H : In _ ( (execute ?T _).(modelElements)) |- _ ] =>
      rewrite (core.Certification.tr_execute_in_elements T) in H ;
      destruct H as [e [H2 H]]

    | [ H : In _ ( (execute ?T _).(modelLinks)) |- _ ] =>
      rewrite (core.Certification.tr_execute_in_links T) in H ;
      destruct H as [e [H2 H]]
  end.


Ltac destruct_instantiatePattern :=
  let H2 := fresh "IN_R" in
  let e := fresh "r" in
  match goal with 
    [ H : In _ (instantiatePattern ?T _ _) |- _ ] =>
      rewrite (core.Certification.tr_instantiatePattern_in T) in H ;
      destruct H as [e [H2 H]]
  end.


Ltac destruct_matchPattern :=
  let H2 := fresh "M" in
  match goal with 
    [ H : In _ (matchPattern ?T _ _) |- _ ] =>
      rewrite (core.Certification.tr_matchPattern_in T) in H ;
      destruct H as [H H2]
  end.



Ltac destruct_instantiateRuleOnPattern :=
  let H2 := fresh "IN_I" in
  let e := fresh "n" in
  match goal with 
    [ H : In _ (instantiateRuleOnPattern _ _ _) |- _ ] =>
      rewrite (core.Certification.tr_instantiateRuleOnPattern_in) in H ;
      destruct H as [e [H2 H]]
  end.


Ltac destruct_instantiateIterationOnPattern :=
  let H2 := fresh "IN_OP" in
  let e := fresh "ope" in
  match goal with 
    [ H : In _ (instantiateIterationOnPattern _ _ _ _) |- _ ] =>
      apply core.Certification.tr_instantiateIterationOnPattern_in in H ;
      destruct H as [e [H2 H]]
  end.


Ltac unfold_instantiateElementOnPattern :=
  match goal with 
    [ H : context[instantiateElementOnPattern _ _ _ _] |- _ ] => 
      rewrite core.Certification.tr_instantiateElementOnPattern_leaf in H 
  end.

Ltac destruct_apply_pattern :=
  let R := fresh "r" in
  let IN1 := fresh "IN_R" in
  let IN2 := fresh "IN" in

  match goal with 
    [ H : In _ (applyPattern ?T _ _) |- _ ] => 
      apply core.Certification.tr_applyPattern_in in H ; 
      destruct H as (R & (IN1 & IN2))
end.

Ltac destruct_applyRuleOnPattern :=
  let N := fresh "n" in 
  let IN1 := fresh "IN" in 
  let IN2 := fresh "IN" in 
  match goal with
    [ H : In _ (applyRuleOnPattern _ _ _ _) |- _ ] =>
      apply core.Certification.tr_applyRuleOnPattern_in in H ;
      destruct H as (N & (IN1 & IN2))
  end.

Ltac destruct_applyIterationOnPattern :=
  let p := fresh "p" in
  let IN1 := fresh "IN" in
  let IN2 := fresh "IN" in
  match goal with
    [ H : In _ (applyIterationOnPattern _ _ _ _ _ ) |- _ ] =>
      apply core.Certification.tr_applyIterationOnPattern_in in H ;
      destruct H as (p & (IN1 & IN2))
  end.

(* on traces *)
Ltac destruct_trace :=
  let p:= fresh "p" in
  let IN := fresh "IN" in
  match goal with 
    [ H: In _ (trace _ _ ) |- _ ] => 
      unfold trace in H ;
      apply in_flat_map in H ; 
      destruct H as (p & (H & IN))
  end.

Ltac destruct_tracePattern :=
  let p:= fresh "r" in
  let IN := fresh "IN" in
  match goal with 
    [ H: In _ (tracePattern _ _ _) |- _ ] => 
      unfold tracePattern in H ;
      apply in_flat_map in H ; 
      destruct H as (p & (H & IN))
  end.


Ltac destruct_traceRuleOnPattern :=
  let p:= fresh "i" in
  let IN := fresh "IN" in
  match goal with 
    [ H: In _ (traceRuleOnPattern _ _ _) |- _ ] => 
      unfold traceRuleOnPattern in H ;
      apply in_flat_map in H ; 
      destruct H as (p & (H & IN))
  end.

Ltac destruct_traceIterationOnPattern :=
  let p:= fresh "e" in
  let IN := fresh "IN" in
  match goal with 
    [ H: In _ (traceIterationOnPattern _ _ _ _) |- _ ] => 
      unfold traceIterationOnPattern in H ;
      apply in_flat_map in H ; 
      destruct H as (p & (H & IN))
  end.



Ltac destruct_in_optionToList :=
  let TMP := fresh "TMP" in
  match goal with 
    [ H : In _ (optionToList ?E) |- _ ] => apply in_optionToList in H
  end.

Lemma in_optionListToList {A} : forall (a:A) b,
    In a (optionListToList b) ->
    exists l, (b = Some l /\ In a l).
Proof.
  intros a b H.
  destruct b ; simpl in H ; [ | contradiction ]. 
  eauto.
Qed.

Ltac destruct_in_optionListToList :=
  let M := fresh "M" in
  match goal with 
    [ H : In _ (optionListToList ?E) |- _ ] => apply in_optionListToList in H ;   destruct H as (l & (M & H))
  end.


Ltac destruct_trace_max := 
  destruct_trace ; 
  destruct_tracePattern ; 
  destruct_traceRuleOnPattern ; 
  destruct_traceIterationOnPattern ; 
  destruct_in_optionToList .


Ltac destruct_any := 
  first [ 
      destruct_execute 
    | destruct_instantiatePattern 
    | destruct_matchPattern 
    | destruct_instantiateRuleOnPattern 
    | destruct_instantiateIterationOnPattern 
    | unfold_instantiateElementOnPattern 
    | destruct_apply_pattern 
    | destruct_applyRuleOnPattern 
    | destruct_applyIterationOnPattern 

    | destruct_trace
    | destruct_tracePattern 
    | destruct_traceRuleOnPattern
    | destruct_traceIterationOnPattern 
    | destruct_in_optionToList].

