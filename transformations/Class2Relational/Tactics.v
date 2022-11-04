
Require Import core.utils.Utils.

Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.


Lemma tables_come_from_classes a b c : 
  In (TableObject a) (instantiatePattern Class2Relational b [c]) ->
  exists d, c = ClassObject d.
Proof.
 destruct c ; simpl ; [ solve [eauto] | intro H ; exfalso ].
 simpl in H.
 destruct a0.
 destruct derived ; simpl in H ; auto.
 destruct H ; auto.
 unfold toModelElement in H.
 simpl in H.
 discriminate H.
Qed.

Lemma columns_come_from_attributes a b c : 
  In (ColumnObject a) (instantiatePattern Class2Relational b [c]) ->
  exists d, c = AttributeObject d.
Proof.
 destruct c ; simpl ; [intro H ; exfalso | solve[eauto] ].
 simpl in H.
 destruct H ; auto.
 unfold toModelElement in H.
 simpl in H.
 discriminate H.
Qed.


Ltac show_origin :=
  let newclassname := fresh "c" in
  let newattributename := fresh "a" in 
  let TMP := fresh in
  match goal with 
   
   [ H : In (TableObject ?a) (instantiatePattern Class2Relational ?b [?c]) |- _ ] =>
      destruct (tables_come_from_classes a b c H) as [newclassname TMP]; subst c

 | [ H : In (ColumnObject ?a) (instantiatePattern Class2Relational ?b [?c]) |- _ ] =>
      destruct (columns_come_from_attributes a b c H) as [newattributename TMP]; subst c

end.


Lemma instpat_singleton : 
  forall m a, instantiatePattern Class2Relational m a <> nil ->
              exists b, a = b::nil.
Proof.
  intros m b H.
  destruct b ; [ | ]. 

  { contradict H ; reflexivity. }
  { destruct b ; [ solve [eauto] | ].
    contradict H. destruct s ; reflexivity.
  }
  
Qed.
  
Lemma in_not_nil {A} (a:A) s :
  In a s -> s <> nil.
Proof.
  intro H.  destruct s ; [ inversion H | congruence]. 
Qed.

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
