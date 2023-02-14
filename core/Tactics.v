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

Ltac destruct_if_goal :=
  let E := fresh "E" in
 match goal with
        [ |- context[if ?B then _ else _] ] => destruct B eqn:E 
 end.

(* To replace the [inversion] tactics on equalities on a dependant type constructor. *)
Ltac dep_inversion H := 
  let H':= fresh H in
  inversion H as [H'] ; apply Eqdep.EqdepTheory.inj_pair2 in H'.

  
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
  match goal with 
    [H:In ?B (instantiatePattern _ ?M ?A) |- _ ] =>

      let TMP1 := fresh "N" in
      let TMP2 := fresh "TMP2" in
      let TMP3 := fresh "TMP3" in
      let E := fresh "e" in
  
      specialize (in_not_nil B (instantiatePattern _ M A) H) ;
      intro TMP1 ; 
      specialize (instpat_singleton _ _ _ _ TMP1) ;
      intro TMP3 ; 
      destruct TMP3 as [ E TMP2] ; 
      [ solve [auto with singleton_rules]
      | subst A (* This [subst] ensures that if A is not a variable, this tactics fails. *) ]
       
  end.




(** ** Destructors *)


Ltac destruct_in_modelElements_execute H :=
  match type of H with 
    In _ ( (execute ?T _).(modelElements))  =>
      let H2 := fresh "IN_E" in
      let e := fresh "sp" in
      rewrite (core.Certification.tr_execute_in_elements T) in H ;
      destruct H as [e [H2 H]]
  end.

Ltac destruct_in_modelLinks_execute H := 
  match type of H with
    In _ (modelLinks (execute ?T _)) =>
      let H2 := fresh "IN_E" in
      let e := fresh "sp" in
      rewrite (core.Certification.tr_execute_in_links T) in H;
      destruct H as [e [H2 H]]                                           end.     

(* deprecated *)
Ltac destruct_execute :=
  match goal with 

    [ H : In _ ( (execute ?T _).(modelElements)) |- _ ] =>
      destruct_in_modelElements_execute H

    | [ H : In _ ( (execute ?T _).(modelLinks)) |- _ ] =>
        destruct_in_modelLinks_execute H
  end.


Ltac destruct_instantiatePattern H IN_MATCH_NEWNAME :=
  match type of H with 
    In _ (instantiatePattern ?T _ _) =>
      let e := fresh "r" in
      rewrite (core.Certification.tr_instantiatePattern_in T) in H ;
      destruct H as [e [IN_MATCH_NEWNAME H]]
  end.

Ltac destruct_instantiatePattern_auto :=
  match goal with 
    [ H : In _ (instantiatePattern ?T _ _) |- _ ] =>
      let H2 := fresh "IN_R" in
      let e := fresh "r" in
      destruct_instantiatePattern H H2
  end.


Ltac destruct_in_matchPattern H NEWNAME :=
  match type of H with 
    | In _ (matchPattern ?T _ _)  =>
      rewrite (core.Certification.tr_matchPattern_in T) in H ;
      destruct H as [H NEWNAME]
  end.

Ltac destruct_in_matchPattern_auto :=
  match goal with 
    [ H : In _ (matchPattern _ _ _) |- _ ] =>
      let H2 := fresh "M" in
      destruct_in_matchPattern H H2
  end.



Ltac destruct_instantiateRuleOnPattern H IN_IT_NEWNAME:=
  match type of H with 
    In _ (instantiateRuleOnPattern _ _ _) =>
      let e := fresh "n" in
      rewrite (core.Certification.tr_instantiateRuleOnPattern_in) in H ;
      destruct H as [e [IN_IT_NEWNAME H]]
  end.

Ltac destruct_instantiateRuleOnPattern_auto :=
  match goal with 
    [ H : In _ (instantiateRuleOnPattern _ _ _) |- _ ] =>
      let H2 := fresh "IN_I" in
      destruct_instantiateRuleOnPattern H H2
  end.


Ltac destruct_instantiateIterationOnPattern H NEWNAME :=
  match type of H with 
    In _ (instantiateIterationOnPattern _ _ _ _) =>
      let e := fresh "ope" in
      apply core.Certification.tr_instantiateIterationOnPattern_in in H ;
      destruct H as [e [NEWNAME H]]
  end.
Ltac destruct_instantiateIterationOnPattern_auto :=
  match goal with 
    [ H : In _ (instantiateIterationOnPattern _ _ _ _) |- _ ] =>
      let H2 := fresh "IN_OP" in
      destruct_instantiateIterationOnPattern H H2
  end.


Ltac unfold_instantiateElementOnPattern H :=
  match type of H with 
    context[instantiateElementOnPattern _ _ _ _] => 
      rewrite core.Certification.tr_instantiateElementOnPattern_leaf in H 
  end.

Ltac unfold_instantiateElementOnPattern_auto :=
  match goal with 
    [ H : context[instantiateElementOnPattern _ _ _ _] |- _ ] => 
      unfold_instantiateElementOnPattern H 
  end.

Ltac destruct_apply_pattern H IN_MATCH_NEWNAME :=
  match type of H with 
    In _ (applyPattern _ _ _) => 
      let R := fresh "r" in
      apply core.Certification.tr_applyPattern_in in H ; 
      destruct H as (R & (IN_MATCH_NEWNAME & H))
end.

Ltac destruct_apply_pattern_auto :=
  match goal with 
    [ H : In _ (applyPattern _ _ _) |- _ ] => 
      let IN1 := fresh "IN_MATCH" in
      destruct_apply_pattern H IN1
end.

Ltac destruct_applyRuleOnPattern :=
  match goal with
    [ H : In _ (applyRuleOnPattern _ _ _ _) |- _ ] =>
      let N := fresh "n" in 
      let IN1 := fresh "IN" in 
      let IN2 := fresh "IN" in 
      apply core.Certification.tr_applyRuleOnPattern_in in H ;
      destruct H as (N & (IN1 & IN2))
  end.

Ltac destruct_applyIterationOnPattern :=
  match goal with
    [ H : In _ (applyIterationOnPattern _ _ _ _ _ ) |- _ ] =>
      let p := fresh "p" in
      let IN1 := fresh "IN" in
      let IN2 := fresh "IN" in
      apply core.Certification.tr_applyIterationOnPattern_in in H ;
      destruct H as (p & (IN1 & IN2))
  end.

(** On traces. *)
Ltac destruct_trace H :=
  match type of H with 
  | In _ (trace _ _ )  => 
      let p:= fresh "p" in
      let IN := fresh "IN" in
      unfold trace in H ;
      apply in_flat_map in H ; 
      destruct H as (p & (IN & H))
  | _ => fail "Failure in destruct_trace."
  end.

Ltac destruct_tracePattern H :=
  match type of H with 
    | In _ (tracePattern _ _ _) => 
        let p:= fresh "r" in
        let IN := fresh "IN" in
        unfold tracePattern in H ;
        apply in_flat_map in H ; 
        destruct H as (p & (IN & H))
  | _ => fail "Failure in destruct_tracePattern."
  end.


Ltac destruct_traceRuleOnPattern H :=
  let p:= fresh "i" in
  let IN := fresh "IN" in
  match type of H  with 
    | In _ (traceRuleOnPattern _ _ _) => 
      unfold traceRuleOnPattern in H ;
      apply in_flat_map in H ; 
      destruct H as (p & (IN & H))
  | _ => fail "Failure in destruct_traceRuleOnPattern."
  end.

Ltac destruct_traceIterationOnPattern H :=
  match type of H with 
    | In _ (traceIterationOnPattern _ _ _ _) => 
        let p:= fresh "e" in
        let IN := fresh "IN" in
        unfold traceIterationOnPattern in H ;
        apply in_flat_map in H ; 
        destruct H as (p & (IN & H))
  | _ => fail "Failure in destruct_traceIterationOnPattern."
  end.



Ltac destruct_in_optionToList H :=
  let TMP := fresh "TMP" in
  match type of H with 
    | In _ (optionToList _) => apply in_optionToList in H
  end.

Ltac destruct_in_optionToList_auto :=
  let TMP := fresh "TMP" in
  match goal with 
    [ H : In _ (optionToList _) |- _ ] => destruct_in_optionToList H
  end.



Ltac chain_destruct_in_trace H := 
  destruct_trace H ; 
  destruct_tracePattern H ; 
  destruct_traceRuleOnPattern H ; 
  destruct_traceIterationOnPattern H ; 
  destruct_in_optionToList H.


(* DEPRECATED : Use chain_destruct_in_modelLinks_execute or chain_destruct_in_modelElements_execute instead *)
Ltac destruct_any := 
  first [ 
      destruct_execute 
    | destruct_instantiatePattern_auto 
    | destruct_in_matchPattern_auto 
    | destruct_instantiateRuleOnPattern_auto 
    | destruct_instantiateIterationOnPattern_auto 
    | unfold_instantiateElementOnPattern_auto 
    | destruct_apply_pattern_auto 
    | destruct_applyRuleOnPattern 
    | destruct_applyIterationOnPattern 
    | destruct_in_optionToList
    ].

Ltac chain_destruct_in_modelElements_execute H :=
  let NEW1 := fresh "IN_M" 
  in
  let NEW2 := fresh "IN_IT" 
  in
  let NEW3 := fresh "IN_OP" 
  in
  let NEW4 := fresh "MATCH_GUARD" 
  in
  let NEW_IN_RULE := fresh "IN_RULE"
  in
  destruct_in_modelElements_execute H ; 
  destruct_instantiatePattern H NEW1 ;
  destruct_instantiateRuleOnPattern H NEW2 ;
  destruct_instantiateIterationOnPattern H NEW3 ;
  unfold_instantiateElementOnPattern H ;
  destruct_in_matchPattern NEW1 NEW4 ;
  rename NEW1 into NEW_IN_RULE.

Ltac chain_destruct_in_modelLinks_execute H :=
  destruct_in_modelLinks_execute H ;
  destruct_apply_pattern_auto ; (* FIXME *)
  destruct_applyRuleOnPattern ;
  destruct_applyIterationOnPattern ; 
  destruct_in_matchPattern_auto.


Ltac simpl_accessors_any H :=
  repeat first [ ConcreteSyntax.simpl_cr_accessors H 
        | ConcreteSyntax.simpl_elem_accessors H 
        | ConcreteSyntax.simpl_link_accessors H
        | Syntax.simpl_r_accessors H 
        | Syntax.simpl_ope_accessors H]. 

Ltac progress_in_In_rules H :=
  match type of H with 
    In ?R (Syntax.rules _) =>
      simpl Syntax.rules in H ;
      progress repeat unfold_In_cons H ;
      subst R
  end.


Ltac exploit_evaloutpat_1 H :=
  match type of H with 
    Expressions.evalOutputPatternElementExpr _ _ _ _ = Some _ =>
      simpl in H ;
      unfold ConcreteExpressions.makeElement in H ;
      unfold ConcreteExpressions.wrapElement in H ; 
      OptionUtils.monadInv H ;
      try discriminate
  end.

Ltac exploit_evaloutpat H :=
  exploit_evaloutpat_1 H ;
  repeat ConcreteExpressions.wrap_inv H.

(** Deprecated : use [exploit_evaloutpat_2] above. *)
Ltac progress_in_evalOutput H :=
  unfold Expressions.evalOutputPatternElementExpr in H ;
  Tactics.simpl_accessors_any H ;
  unfold ConcreteExpressions.makeElement in H ;
  unfold ConcreteExpressions.wrapElement in H ;
  OptionUtils.monadInv H ;
  repeat ConcreteExpressions.wrap_inv H ;
  try discriminate.

Ltac progress_in_ope H :=
  match type of H with 
  | In ?ope (Syntax.r_outputPattern (Parser.parseRule (ConcreteSyntax.Build_ConcreteRule _ _ _ _ _ ))) => 
 
      unfold Parser.parseRule in H ;
      unfold Syntax.r_outputPattern in H ; 
      unfold ConcreteSyntax.r_outpat in H ;
      unfold List.map in H ;
      progress repeat unfold_In_cons H ;
      subst ope 
            
  | In ?ope (Syntax.r_outputPattern (Parser.parseRule ?E)) =>
       progress unfold E in H ; (* for the case where a rule is defined outsoide the transformation *)
      progress_in_ope H (* recursion *)

  | In ?ope (Syntax.r_outputPattern (Parser.parseRule _)) =>
      fail "ConcreteRule must be unfolded"
  end.

Ltac exploit_in_it H :=
  match type of H with
  | In ?I (seq _ (Expressions.evalIteratorExpr (Parser.parseRule (ConcreteSyntax.Build_ConcreteRule _ _ _ _ _ )) _ _)) => 
      unfold Parser.parseRule in H ; 
      unfold Expressions.evalIteratorExpr in H ; 
      unfold Syntax.r_iterator in H ; 
      unfold ConcreteSyntax.r_iter in H ;
      simpl seq in H ;
      repeat unfold_In_cons H ;
      subst I
  | In _ (seq _ (Expressions.evalIteratorExpr (Parser.parseRule ?E) _ _)) => 
      progress unfold E in H ; 
      exploit_in_it H (* recursion *)
  end.
  
Ltac exploit_evalGuard H :=
    match type of H with
      | Expressions.evalGuardExpr (Parser.parseRule (ConcreteSyntax.Build_ConcreteRule _ _ _ _ _)) _ _ = true => 
          unfold Parser.parseRule in H ;
          unfold Expressions.evalGuardExpr in H ; 
          unfold Syntax.r_guard in H ; 
          unfold ConcreteSyntax.r_guard in H ; 
          unfold ConcreteSyntax.r_InKinds in H ; 
          first [ progress unfold ConcreteExpressions.makeEmptyGuard in H  
                | progress unfold ConcreteExpressions.makeGuard in H] ;
            
          ConcreteExpressions.monadInv H ;
          repeat ConcreteExpressions.wrap_inv H 
      
    | Expressions.evalGuardExpr (Parser.parseRule ?R) _ _ = true =>
          progress unfold R in H ;
          exploit_evalGuard H (* recursion *)
    end.

(** Tactics to progress in the goal (not in the hypothesis) *)

Ltac destruct_in_trace_G :=
  match goal with 
    [ |- In _ (trace _ _)] => 
      unfold trace ;
      apply in_flat_map
  end.
