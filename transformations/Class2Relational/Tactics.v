
Require Import core.utils.Utils.

Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

(** ** Type correspondence *)

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

(** ** Size of patterns *)

(** *** One-to-one rules and transformations *)

(** We say a rule is one-to-one rule when it matches singletons. *)

Definition one_to_one_rule (r: Syntax.Rule) : Prop := 
  match r with 
    Syntax.buildRule _ b _ _ =>
      (forall m, b m nil = None) /\
        (forall m e1 e2 r, b m (e1 :: e2 :: r) = None)
  end.


Lemma one_to_one_nil_false : 
  forall a, 
    one_to_one_rule a ->
    forall m,
      matchRuleOnPattern a m nil = false.
Proof.
  intros a A m.
  destruct a.
  unfold matchRuleOnPattern ; simpl in *.
  destruct A as [A _].
  rewrite A.
  reflexivity.
Qed.


Lemma one_to_one_two_false : 
  forall a, 
    one_to_one_rule a ->
    forall m e1 e2 r,
      matchRuleOnPattern a m (e1::e2::r) = false.
Proof.
  intros a A m e1 e2 r.
  destruct a.
  unfold matchRuleOnPattern ; simpl in *.
  destruct A as [_ A].
  rewrite A.
  reflexivity.
Qed.

(** *** Singleton-pattern rules and transformations *)


(** We say a rule has a singleton-pattern when it pattern is a list of size 1. *)
Definition singleton_pattern_rule a :=
  match a with 
  | (ConcreteSyntax.concreteRule s [m] o o0 l) => True
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
  destruct InTypes ; try contradiction.
  destruct InTypes ; try contradiction.
  clear H.
  simpl.
  split ; intro m ; [ | ].
  {
    destruct o ; simpl ; reflexivity.
  }
  {
    intros e1 e2 r.
    destruct o ; simpl.
    { unfold ConcreteExpressions.makeGuard. simpl.
      Set Printing All. 
      destruct (@toModelClass ClassM ClassMetamodel s0 e1) ; reflexivity.

    }
    {
      destruct (@toModelClass ClassM ClassMetamodel s0 e1) ; reflexivity. 
    }
  }
Qed.


(** We say a transformation is one-to-one when its rules are one-to-one. *)

Definition one_to_one_transformation :
  Syntax.Transformation -> Prop :=
  fun a => 
    match a with  
      Syntax.buildTransformation _ b =>
        List.Forall one_to_one_rule b
    end.

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

(** *** Properties/Tactics on [instantiatePattern] for one-to-one transformations *)

Lemma instpat_nil : 
  forall t, 
    one_to_one_transformation t ->
    forall m,
      instantiatePattern t m nil = nil.
Proof.
  intro t ; destruct t ; simpl.
  unfold instantiatePattern ; simpl.
  unfold matchPattern ; simpl.
  induction l ; intros A m ; inversion_clear A ; simpl ; [reflexivity | ].
  rewrite one_to_one_nil_false ; auto.
Qed.

Lemma instpat_two : 
  forall t, 
    one_to_one_transformation t ->
    forall m e1 e2 r,
      instantiatePattern t m (e1 :: e2 :: r) = nil.
Proof.
  intros t ; destruct t ; simpl.
  unfold instantiatePattern ; simpl.
  unfold matchPattern ; simpl.
  induction l ; intros A m e1 e2 r; inversion_clear A ; simpl ; [reflexivity | ].
  rewrite one_to_one_two_false ; auto.
Qed.


Lemma instpat_singleton_gen : 
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


Lemma in_not_nil {A} (a:A) s :
  In a s -> s <> nil.
Proof.
  intro H.  destruct s ; [ inversion H | congruence]. 
Qed.

(** *** Application to [Class2Relational] *)

Lemma class2relational_one_to_one : 
  one_to_one_transformation Class2Relational.
Proof.
  apply one_to_one_transformation_parse.
  unfold Class2Relational' ; unfold singleton_pattern_transformation ; simpl ; repeat constructor.
Qed.

Lemma instpat_singleton : 
  forall m a, instantiatePattern Class2Relational m a <> nil ->
              exists b, a = b::nil.
Proof.
  apply instpat_singleton_gen.
  apply class2relational_one_to_one.
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
