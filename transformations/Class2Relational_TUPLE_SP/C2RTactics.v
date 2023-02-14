
Require Import String.

Require Import core.utils.Utils.

Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational_TUPLE_SP.Class2Relational_TUPLE_SP.
Require Import transformations.Class2Relational_TUPLE_SP.ClassMetamodel.
Require Import transformations.Class2Relational_TUPLE_SP.RelationalMetamodel.

From core Require Tactics Certification.

(** ** Type correspondence *)

Lemma tables_come_from_classes a b c : 
  In (TableElement a) (instantiatePattern Class2Relational_TUPLE_SP b [c]) ->
  exists d, c = ClassElement d.
Proof.
 destruct c ; simpl ; [ solve [eauto] | intro H ; exfalso ].
 inversion H.
Qed.

Lemma columns_come_from_attributes a b c d : 
  In (ColumnElement a) (instantiatePattern Class2Relational_TUPLE_SP b [c; d]) ->
  exists e f, c = AttributeElement e /\
              d = ClassElement f.
Proof.
 intro.
 destruct c.
 { simpl in H. inversion H. }
 { simpl in H. destruct d.
   { exists a0, c. auto. }
   { simpl in H. inversion H.  }
 }
Qed.


Ltac show_origin :=
  let newclassname := fresh "c" in
  let newattributename := fresh "a" in 
  let TMP := fresh in
  match goal with 
   
   [ H : In (TableElement ?a) (instantiatePattern Class2Relational_TUPLE_SP ?b [?c]) |- _ ] =>
      destruct (tables_come_from_classes a b c H) as [newclassname TMP]; subst c

 | [ H : In (ColumnElement ?a) (instantiatePattern Class2Relational_TUPLE_SP ?b [?c; ?d]) |- _ ] =>
      destruct (columns_come_from_attributes a b c d H) as [newattributename TMP]; subst c

end.


Lemma unify_table_class_lem :
  forall cm c ta,
    In (TableElement ta)
      (instantiatePattern Class2Relational_TUPLE_SP cm [ClassElement c]) ->
    ta = {| table_id := class_id c; table_name := class_name c |}.
Proof.
  intros cm c ta H.
  compute in H.
  remove_or_false H.
  PropUtils.inj H.
  reflexivity.
Qed.


Ltac unify_table_class_tac H :=
  match type of H with
    In (TableElement ?ta) (instantiatePattern Class2Relational_TUPLE_SP _ [ClassElement ?c]) => apply unify_table_class_lem in H ; subst ta
  end.

Lemma unify_column_attribute_lem : 
  forall m a cl c, 
  In (ColumnElement c)
          (instantiatePattern Class2Relational_TUPLE_SP m
             [AttributeElement a; ClassElement cl]) ->
  c = {| column_id := a.(attr_id); column_name := a.(attr_name) |} /\ 
  a.(derived) = false /\
  (getAttributeType a m) = Some cl.
Proof.
  intros.
  unfold instantiatePattern in H. unfold matchPattern in H. simpl in H.
  unfold ConcreteExpressions.makeGuard in H. simpl in H. 
  destruct (derived a).
  { simpl in H. inversion H. }
  { simpl in H. 
    destruct (getAttributeType a m).
    { simpl in H. 
      destruct (beq_Class cl c0) eqn: ca.
      { simpl in H. remove_or_false H.
        PropUtils.inj H. split.
        reflexivity. split. reflexivity.
        apply lem_beq_Class_id in ca.
        rewrite ca. reflexivity. }
      { simpl in H. inversion H. } 
    }
    { simpl in H. inversion H. } 
  }
Qed.

Ltac unify_column_attribute_tac H :=
  let H2 := fresh in
  match type of H with 
    In (ColumnElement ?c)
      (instantiatePattern Class2Relational_TUPLE_SP _
         [AttributeElement ?a; ClassElement ?cl]) => 
          apply unify_column_attribute_lem in H ; destruct H as [H2 H] ; subst c
  end.

(*
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

Lemma make1_alt sm e :
  ConcreteExpressions.makeEmptyGuard [Class_K] sm e = true ->
  exists v, e = [ClassElement v]. 
Proof.
  destruct e ; intro H. 
  + discriminate H.  
  + destruct e.
    - apply make1 in H. destruct H ; subst ; eauto.
    - compute in  H. 
      destruct s ; discriminate .
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

Lemma make2_alt sm e:
  ConcreteExpressions.makeGuard [Attribute_K]
    (fun (_ : TransformationConfiguration.SourceModel)
         (a : Attribute_t) => negb (derived a)) sm 
    e = true -> exists v, (e = [AttributeElement v] /\ v.(derived) = false).
Proof.
  destruct e ; intro.
  + discriminate H.
  + destruct e.
  - apply make2 in H.
    destruct H as (? & (? & ?)) ; subst.
    eauto.
  - compute in H. 
    destruct s ; discriminate H.
Qed.



Ltac deduce_element_kind_from_guard :=
  let H2 := fresh "D" in
  let a := fresh "a" in
  match goal with 
    [ H :ConcreteExpressions.makeEmptyGuard [Class_K] _ [?e] = true |- _ ] =>
      apply make1 in H ; destruct H ; subst e

    | [ H :ConcreteExpressions.makeEmptyGuard [Class_K] _ ?e = true |- _ ] =>
      apply make1_alt in H ; destruct H ; subst e


  | [ H :ConcreteExpressions.makeGuard [Attribute_K]
    (fun _ atr => negb (derived atr)) _ 
    [?e] = true |- _ ] =>
      apply make2 in H ; destruct H as (a & (H & H2)) ; 
      first[ subst e (* if e was a variable *) 
             | Tactics.inj H (* if e was not a variable *) ]

  | [ H :ConcreteExpressions.makeGuard [Attribute_K]
    (fun _ atr => negb (derived atr)) _ 
    ?e = true |- _ ] =>
      apply make2_alt in H ; destruct H as (a & (H & H2)) ; 
      (*first[*) subst e (* if e was a variable *) 
             (*| Tactics.inj H (* if e was not a variable *) ]*)
end.


(** ** Size of patterns *)

Lemma one_to_one : 
  Tactics.singleton_transformation_a _ Class2Relational.
Proof.
  apply Tactics.singleton_transformation_parse.
  unfold Class2Relational' ; unfold Tactics.singleton_transformation_a ; simpl ; repeat constructor.
Qed.

Hint Resolve one_to_one : singleton_rules.


(** ** Destructors *)

Ltac destruct_In_two :=
  match goal with 
    [ H : In ?X Class2Relational.(Syntax.rules) |- _ ] => 
      simpl in H ; 
      unfold In in H ; (* force it because simpl In can be disabled by Arguments In: simpl never. *)

      repeat destruct_or H ; [ | | contradiction H] ; subst X
  end.*)


(** *** Utilities on [allTuples] *)


Lemma allModelElements_allTuples e (cm:Model ClassMM): 
  In e cm.(modelElements) ->
  In [e] (allTuples Class2Relational_TUPLE_SP cm).
Proof. 
  intro.
  apply (Tactics.allModelElements_allTuples (tc:=C2RConfiguration)); auto.
  compute.
  auto.
Qed. 

(** Specific tactics for this transformation. *)
Ltac exploit_guard H := 
  match type of H with
    andb (negb _) (is_option_eq _ _ _) = true =>
      apply eq_sym in H ; 
      apply Bool.andb_true_eq in H ;
      let NEW := fresh H in
      destruct H as [H NEW] ;
      apply eq_sym in H ;
      apply eq_sym in NEW ; 
      apply Bool.negb_true_iff in H ;
      OptionUtils.is_option_eq_inv NEW
  end.
