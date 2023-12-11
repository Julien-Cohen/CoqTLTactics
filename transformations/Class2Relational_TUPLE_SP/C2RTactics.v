
Require Import String.

Require Import core.utils.Utils.

Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational_TUPLE_SP.Class2Relational_TUPLE_SP.
Require Import transformations.Class2Relational_TUPLE_SP.ClassMetamodel.
Require Import transformations.Class2Relational_TUPLE_SP.RelationalMetamodel.

From usertools Require TacticsFW.

(** ** Type correspondence *)

Lemma tables_come_from_classes a b c : 
  In (TableElement a) (produced_elements (traceTrOnPiece Class2Relational_TUPLE_SP b [c])) ->
  exists d, c = ClassElement d.
Proof.
 destruct c ; simpl ; [ solve [eauto] | intro H ; exfalso ].
 inversion H.
Qed.

Lemma columns_come_from_attributes a b c d : 
  In (ColumnElement a) (produced_elements (traceTrOnPiece Class2Relational_TUPLE_SP b [c; d])) ->
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
   
   [ H : In (TableElement ?a) (produced_elements (traceTrOnPiece Class2Relational_TUPLE_SP ?b [?c])) |- _ ] =>
      destruct (tables_come_from_classes a b c H) as [newclassname TMP]; subst c

 | [ H : In (ColumnElement ?a) (produced_elements (traceTrOnPiece Class2Relational_TUPLE_SP ?b [?c; ?d])) |- _ ] =>
      destruct (columns_come_from_attributes a b c d H) as [newattributename TMP]; subst c

end.


Lemma unify_table_class_lem :
  forall cm c ta,
    In (TableElement ta)
      (produced_elements (traceTrOnPiece Class2Relational_TUPLE_SP cm [ClassElement c])) ->
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
    In (TableElement ?ta) (produced_elements (traceTrOnPiece Class2Relational_TUPLE_SP _ [ClassElement ?c])) => apply unify_table_class_lem in H ; subst ta
  end.

Lemma unify_column_attribute_lem : 
  forall m a cl c, 
  In (ColumnElement c)
          (produced_elements (traceTrOnPiece Class2Relational_TUPLE_SP m
             [AttributeElement a; ClassElement cl])) ->
  c = {| column_id := a.(attr_id); column_name := a.(attr_name) |} /\ 
  a.(derived) = false /\
  (getAttributeType a m) = Some cl.
Proof.
  intros.
  unfold traceTrOnPiece in H. 
  unfold matchingRules in H.
  simpl in H.
  unfold ConcreteExpressions.makeGuard in H. simpl in H. 
  destruct (derived a).
  { simpl in H. inversion H. }
  { simpl in H. 
    destruct (getAttributeType a m).
    { simpl in H. 
      destruct (Class_t_beq cl c0) eqn: ca.
      { simpl in H. remove_or_false H.
        PropUtils.inj H. split.
        reflexivity. split. reflexivity.
        apply internal_Class_t_dec_bl in ca.
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
      (produced_elements (traceTrOnPiece Class2Relational_TUPLE_SP _
         [AttributeElement ?a; ClassElement ?cl])) => 
          apply unify_column_attribute_lem in H ; destruct H as [H2 H] ; subst c
  end.



(** *** Utilities on [allTuples] *)


Lemma allModelElements_allTuples e (cm:Model ClassMM): 
  In e cm.(modelElements) ->
  In [e] (allTuples Class2Relational_TUPLE_SP cm).
Proof. 
  intro.
  apply <- Semantics.in_allTuples_incl_singleton.
  compute ; auto.
Qed. 

(** * Specific tactics for this transformation. *)
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
