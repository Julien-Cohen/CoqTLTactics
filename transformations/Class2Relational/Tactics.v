
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
 remove_or_false H.
 discriminate H.
Qed.

Lemma columns_come_from_attributes a b c : 
  In (ColumnElement a) (instantiatePattern Class2Relational b [c]) ->
  exists d, c = AttributeElement d.
Proof.
 destruct c ; simpl ; [intro H ; exfalso | solve[eauto] ].
 simpl in H.
 remove_or_false H.
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


Lemma unify_table_class_lem :
  forall cm c ta,
    In (TableElement ta)
      (instantiatePattern Class2Relational cm [ClassElement c]) ->
    ta = {| table_id := class_id c; table_name := class_name c |}.
Proof.
  intros cm c ta H.
  compute in H.
  remove_or_false H.
  Tactics.inj H.
  reflexivity.
Qed.

Ltac unify_table_class_tac H :=
  match type of H with
    In (TableElement ?ta) (instantiatePattern Class2Relational _ [ClassElement ?c]) => apply unify_table_class_lem in H ; subst ta
  end.

Lemma unify_column_attribute_lem : 
  forall m a c, 
  In (ColumnElement c)
          (instantiatePattern Class2Relational m
             [AttributeElement a]) ->
  c = {| column_id := a.(attr_id); column_name := a.(attr_name) |} /\ a.(derived) = false.
Proof.
  intros m a c H ; destruct a ; simpl.
  destruct derived ; compute in H ; [ contradiction H | remove_or_false H ].
  Tactics.inj H.
  auto.
Qed.

Ltac unify_column_attribute_tac H :=
  let H2 := fresh in
  match type of H with 
    In (ColumnElement ?c)
      (instantiatePattern Class2Relational _
         [AttributeElement ?a]) => apply unify_column_attribute_lem in H ; destruct H as [H2 H] ; subst c
  end.

Ltac unify_all :=
  match goal with
    [ H : In (ColumnElement _) (instantiatePattern Class2Relational _ [AttributeElement _]) |- _ ] =>
      unify_column_attribute_tac H

   | [ H : In (TableElement _) (instantiatePattern Class2Relational _ [ClassElement _]) |- _ ] => unify_table_class_tac H
  end.

Lemma make1 sm e :
  ConcreteExpressions.makeEmptyGuard [Class_K] sm [e] = true ->
  exists v, e = ClassElement v. 
Proof.
  destruct e ; compute ; intro M ; [ eauto | discriminate].
Qed.

Lemma make2 sm e:
  ConcreteExpressions.makeGuard [Attribute_K]
    (fun (_ : TransformationConfiguration.SourceModel)
         (a : Attribute_t) => negb (derived a)) sm 
    [e] = true -> exists v, (e = AttributeElement v /\ v.(derived) = false).
Proof.
  destruct e ; [ discriminate | ] ; compute.
  destruct a.
  destruct derived ; [ discriminate | ].
  eauto.
Qed.



Ltac deduce_element_kind_from_guard :=
  let H2 := fresh "D" in
  let a := fresh "a" in
  match goal with 
    [ H :ConcreteExpressions.makeEmptyGuard [Class_K] _ [?e] = true |- _ ] =>
      apply make1 in H ; destruct H ; subst e

  | [ H :ConcreteExpressions.makeGuard [Attribute_K]
    (fun _ atr => negb (derived atr)) _ 
    [?e] = true |- _ ] =>
      apply make2 in H ; destruct H as (a & (H & H2)) ; 
      first[ subst e (* if e was a variable *) 
             | Tactics.inj H (* if e was not a variable *) ]
end.


(** ** Size of patterns *)

Lemma one_to_one : 
  Tactics.singleton_transformation_a _ Class2Relational.
Proof.
  apply Tactics.singleton_transformation_parse.
  unfold Class2Relational' ; unfold Tactics.singleton_transformation_a ; simpl ; repeat constructor.
Qed.

Hint Resolve one_to_one : singleton_rules.

(** Tactics to make appear that a sucessfully matched pattern is a singleton. *) 

Ltac show_singleton :=
  let TMP1 := fresh "TMP" in
  let TMP2 := fresh "TMP" in
  let E := fresh "e" in
  match goal with 
    [H:In ?B (instantiatePattern Class2Relational ?M ?A) |- _ ] =>
  
      specialize (in_not_nil B (instantiatePattern Class2Relational M A) H) ;
      intro TMP ;
      destruct (Tactics.instpat_singleton _ Class2Relational _ _ TMP1) as [ E TMP2 ];
      [ solve [auto with singleton_rules]
      | clear TMP1 ; subst A (* This [subst] ensures that if A is not a variable, this tactics fails. *) ]

  end.

(** ** Destructors *)

Ltac destruct_execute :=
  let H2 := fresh "IN_E" in
  let e := fresh "sp" in
  match goal with 
    [ H : In _ ( (execute Class2Relational _).(modelElements)) |- _ ] =>
      rewrite (core.Certification.tr_execute_in_elements Class2Relational) in H ;
      destruct H as [e [H2 H]]
  end.

Ltac destruct_instantiatePattern :=
  let H2 := fresh "IN_R" in
  let e := fresh "r" in
  match goal with 
    [ H : In _ (instantiatePattern Class2Relational _ _) |- _ ] =>
      rewrite (core.Certification.tr_instantiatePattern_in Class2Relational) in H ;
      destruct H as [e [H2 H]]
  end.

Ltac destruct_matchPattern :=
  let H2 := fresh "M" in
  match goal with 
    [ H : In _ (matchPattern Class2Relational _ _) |- _ ] =>
      rewrite (core.Certification.tr_matchPattern_in Class2Relational) in H ;
      destruct H as [H H2]
  end.

Ltac destruct_instantiateRuleOnPattern :=
  let H2 := fresh "IN_I" in
  let e := fresh "n" in
  match goal with 
    [ H : In _ (instantiateRuleOnPattern _ _ _) |- _ ] =>
      rewrite (core.Certification.tr_instantiateRuleOnPattern_in Class2Relational) in H ;
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


Ltac destruct_any := first [ destruct_execute | destruct_instantiatePattern | destruct_matchPattern | destruct_instantiateRuleOnPattern | destruct_instantiateIterationOnPattern | unfold_instantiateElementOnPattern ].

Ltac destruct_In_two :=
  match goal with 
    [ H : In ?X Class2Relational.(Syntax.rules) |- _ ] => 
      simpl in H ; 
      unfold In in H ; (* force it because simpl In can be disabled by Arguments In: simpl never. *)

      repeat destruct_or H ; [ | | contradiction H] ; subst X
  end.


(** *** Utilities on [allTuples] *)


Lemma allModelElements_allTuples e (cm:Model ClassMM): 
  In e cm.(modelElements) ->
  In [e] (allTuples Class2Relational cm).
Proof. 
  intro.
  apply (Tactics.allModelElements_allTuples (tc:=C2RConfiguration)); auto.
Qed.
