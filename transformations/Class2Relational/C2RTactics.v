
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
    In (TableElement ?ta) (instantiatePattern Class2Relational _ [ClassElement ?c]) => 
      apply unify_table_class_lem in H ;
      subst ta
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
  match type of H with 
    In (ColumnElement ?c)
      (instantiatePattern Class2Relational _
         [AttributeElement ?a]) => 
      let H2 := fresh in
      apply unify_column_attribute_lem in H ;
      destruct H as [H2 H] ;
      subst c
  end.


Ltac unify_all :=
  match goal with
    [ H : In (ColumnElement _) (instantiatePattern Class2Relational _ [AttributeElement _]) |- _ ] =>
      unify_column_attribute_tac H

   | [ H : In (TableElement _) (instantiatePattern Class2Relational _ [ClassElement _]) |- _ ] => 
       unify_table_class_tac H
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
      first[ 
          subst e (* if e was a variable *) 
        | Tactics.inj H (* if e was not a variable *) 
        ]

  | [ H :ConcreteExpressions.makeGuard [Attribute_K] (fun _ atr => negb (derived atr)) _  ?e = true |- _ ] =>
      apply make2_alt in H ;
      destruct H as (a & (H & H2)) ; 
       subst e (* if e was a variable *) 
             
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

Lemma in_rules : forall r, 
    In r (Syntax.rules Class2Relational) ->
    r = core.modeling.Parser.parseRule Class2Relational.R1 \/ r = core.modeling.Parser.parseRule Class2Relational.R2.
Proof.
  unfold Class2Relational.
  unfold Class2Relational'.
  simpl.
  intros ; auto.
  repeat destruct_or H ; [ auto | auto | contradiction ].
Qed.


Ltac choose_rule :=
  match goal with 
    [ H : In ?X Class2Relational.(Syntax.rules) |- _ ] => 
      apply in_rules in H ;
      destruct_or H ; 
      subst X
  end.


(** *** Utilities on [allTuples] *)


Lemma allModelElements_allTuples e (cm:Model ClassMM): 
  In e cm.(modelElements) ->
  In [e] (allTuples Class2Relational cm).
Proof. 
  intro.
  apply (Tactics.allModelElements_allTuples (tc:=C2RConfiguration));
    auto.
Qed.

Lemma in_allTuples_singleton :
  forall e t s, 
    In [e] (allTuples t s) ->
    In e s.(modelElements).
Proof.
  intros e t s IN.
  apply incl_singleton.
  eapply Certification.allTuples_incl.
  exact IN.
Qed.

(** *** January tactics *)


Ltac progress_in_guard H :=
  first [ progress unfold R1 in H | progress unfold R2 in H ] ;
  Parser.unfold_parseRule H ; 
  Tactics.simpl_accessors_any H ;
  unfold Expressions.evalGuardExpr in H ;
  Tactics.simpl_accessors_any H ;
  deduce_element_kind_from_guard.


Ltac progress_in_ope H ope :=
  first [ progress unfold R1 in H | progress unfold R2 in H ] ;
  Parser.unfold_parseRule H ; 
  Tactics.simpl_accessors_any H ;
  unfold map in H ; 
  Tactics.simpl_accessors_any H ;
  apply in_singleton in H ;
  subst ope.


Ltac progress_in_evalOutput H :=
  unfold Expressions.evalOutputPatternElementExpr in H ;
  Tactics.simpl_accessors_any H ;
  unfold ConcreteExpressions.makeElement in H ;
  unfold ConcreteExpressions.wrapElement in H ;
  OptionUtils.monadInv H ;
  simpl ConcreteExpressions.wrap in H ;
  first [ discriminate | Tactics.inj H ].

Ltac unfold_traceElementOnPattern H :=
  match type of H with
  | traceElementOnPattern _ _ _ _ = return _ => 
      unfold traceElementOnPattern in H ; OptionUtils.monadInv H
  end.

Ltac progress_in_traceElementOnPattern H := 
  unfold_traceElementOnPattern H ;
  Tactics.unfold_instantiateElementOnPattern ; 
  C2RTactics.progress_in_evalOutput H.


Ltac unfold_toEData H :=
  unfold toEData in H ;
  simpl (unbox _) in H ;
  unfold get_E_data in H.

Ltac unfold_make_element H :=
  unfold ConcreteExpressions.makeElement in H ;
  unfold ConcreteExpressions.wrapElement in H ;
  unfold ConcreteExpressions.wrap in H ;
  unfold_toEData H ;
  unfold ClassMetamodel.get_E_data in H.

Ltac unfold_make_link H := 
  unfold ConcreteExpressions.makeLink in H ;
  unfold ConcreteExpressions.wrapLink in H ;
  unfold ConcreteExpressions.wrap in H;
  unfold_toEData H ;
  unfold ClassMetamodel.get_E_data in H.
