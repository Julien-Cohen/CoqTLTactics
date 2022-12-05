
Require Import core.utils.Utils.

Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From core Require Tactics Certification.

(** ** Type correspondence *)

Lemma tables_come_from_classes a b c : 
  In (TableElement a) (instantiatePattern Class2Relational b [c]) ->
  exists d, c = ClassElement d.
Proof.
 destruct c ; simpl ; [ solve [eauto] | intro H ; exfalso ].
 simpl in H.
 destruct a0.
 destruct derived ; simpl in H ; auto.
 destruct_or H ; [ | contradiction].
 unfold toModelElement in H.
 simpl in H.
 discriminate H.
Qed.

Lemma columns_come_from_attributes a b c : 
  In (ColumnElement a) (instantiatePattern Class2Relational b [c]) ->
  exists d, c = AttributeElement d.
Proof.
 destruct c ; simpl ; [intro H ; exfalso | solve[eauto] ].
 simpl in H.
 destruct_or H ; [ | contradiction ].
 unfold toModelElement in H.
 simpl in H.
 discriminate H.
Qed.


Ltac show_origin :=
  let newclassname := fresh "c" in
  let newattributename := fresh "a" in 
  let TMP := fresh in
  match goal with 
   
   [ H : In (TableElement ?a) (instantiatePattern Class2Relational ?b [?c]) |- _ ] =>
      destruct (tables_come_from_classes a b c H) as [newclassname TMP]; subst c

 | [ H : In (ColumnElement ?a) (instantiatePattern Class2Relational ?b [?c]) |- _ ] =>
      destruct (columns_come_from_attributes a b c H) as [newattributename TMP]; subst c

end.

(** ** Size of patterns *)

Lemma one_to_one : 
  Tactics.one_to_one_transformation _ Class2Relational.
Proof.
  apply Tactics.one_to_one_transformation_parse.
  unfold Class2Relational' ; unfold Tactics.singleton_pattern_transformation ; simpl ; repeat constructor.
Qed.

Lemma instpat_singleton : 
  forall m a, instantiatePattern Class2Relational m a <> nil ->
              exists b, a = b::nil.
Proof.
  apply Tactics.instpat_singleton.
  apply one_to_one.
Qed.

(** Tactics to make appear that a sucessfully matched pattern is a singleton. *) 

Ltac show_singleton :=
  let TMP := fresh in
  match goal with 
    [H:In ?B (instantiatePattern Class2Relational ?M ?A) |- _ ] =>
  
      specialize (in_not_nil B (instantiatePattern Class2Relational M A) H) ;
      intro TMP ;
      apply instpat_singleton in TMP ;
      destruct TMP ;
      subst A (* This [subst] ensures that if A is not a variable, this tactics fails. *)
  end.

(** ** Destructors *)

Ltac destruct_execute :=
  let H2 := fresh "H" in
  let e := fresh "sp" in
  match goal with 
    [ H : In _ ( (execute Class2Relational _).(modelElements)) |- _ ] =>
      rewrite (core.Certification.tr_execute_in_elements Class2Relational) in H ;
      destruct H as [e [H H2]]
  end.

Ltac destruct_instantiatePattern :=
  let H2 := fresh "H" in
  let e := fresh "x" in
  match goal with 
    [ H : In _ (instantiatePattern Class2Relational _ _) |- _ ] =>
      rewrite (core.Certification.tr_instantiatePattern_in Class2Relational) in H ;
      destruct H as [e [H H2]]
  end.

Ltac destruct_matchPattern :=
  let H2 := fresh "H" in
  match goal with 
    [ H : In _ (matchPattern Class2Relational _ _) |- _ ] =>
      rewrite (core.Certification.tr_matchPattern_in Class2Relational) in H ;
      destruct H as [H H2]
  end.

Ltac destruct_instantiateRuleOnPattern :=
  let H2 := fresh "H" in
  let e := fresh "x" in
  match goal with 
    [ H : In _ (instantiateRuleOnPattern _ _ _) |- _ ] =>
      rewrite (core.Certification.tr_instantiateRuleOnPattern_in Class2Relational) in H ;
      destruct H as [e [H H2]]
  end.

Ltac destruct_instantiateIterationOnPattern :=
  let H2 := fresh "H" in
  let e := fresh "ope" in
  match goal with 
    [ H : In _ (instantiateIterationOnPattern _ _ _ _) |- _ ] =>
      apply core.Certification.tr_instantiateIterationOnPattern_in in H ;
      destruct H as [e [H H2]]
  end.

Ltac unfold_instantiateElementOnPattern :=
  match goal with 
    [ H : context[instantiateElementOnPattern _ _ _ _] |- _ ] => 
      rewrite core.Certification.tr_instantiateElementOnPattern_leaf in H 
  end.


Ltac destruct_any := first [ destruct_execute | destruct_instantiatePattern | destruct_matchPattern | destruct_instantiateRuleOnPattern | destruct_instantiateIterationOnPattern | unfold_instantiateElementOnPattern ].

Ltac destruct_In_two :=
  match goal with 
    [ H : In ?X Class2Relational.(Syntax.rules) |- _ ] => 
      simpl in H ;
      repeat destruct_or H ; [ | | contradiction H] ; subst X
  end.

