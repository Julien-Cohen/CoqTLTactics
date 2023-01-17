
Require Import List.

Require Import core.utils.Utils.
Require Import core.Model.

From transformations.Class2Relational Require Import ClassMetamodel.

From transformations.Class2Relational Require Tactics.

(* Used *)
Lemma getAttributeTypeOnLinks_In_right l t v : 
  getAttributeTypeOnLinks v l = return t ->
    In (AttributeTypeLink {| source_attribute  := v ; a_type := t |}) l.
Proof.
  induction l ; simpl ; intro G ; [ discriminate | ].
  destruct a.
  { (*ClassAttributeLink*)
    apply IHl in G ; clear IHl.
    right ; assumption.
  }
  { (*AttributeTypeLink*)
    Tactics.destruct_if_hyp.
    { (* true *)
      Tactics.inj G.
      apply lem_beq_Attribute_id in E.
      destruct a ; subst ; simpl in *.
      left ; reflexivity.
    }
    {
      (* false *)
      clear E.
      apply IHl in G ; clear IHl.
      right ; assumption.
    }
  }
Qed.


(* Used *)
Corollary getAttributeType_In_right att m t: 
  getAttributeType att m = Some t ->
    In (AttributeTypeLink {| source_attribute := att ; a_type := t |}) m.(modelLinks).
Proof.
  unfold getAttributeType.
  apply getAttributeTypeOnLinks_In_right. 
Qed. 

(* Used *)
Lemma getAttributeType_In_left att t (m:Model ClassMM): 
  In (AttributeTypeLink {| source_attribute := att ; a_type := t |}) m.(modelLinks) ->
  getAttributeType att m <> None.
Proof.
  destruct m. simpl.
  unfold getAttributeType ; simpl.
  clear modelElements.
  induction modelLinks ; simpl ; [ congruence | ] ; intro.
  destruct a.
  + (* ClassAttibute *)
    destruct_or H ; [discriminate|].
    apply IHmodelLinks in H ; clear IHmodelLinks.
    exact H.
  + (* AttributeType *)
    destruct a.
    destruct_or H.
  - injection H ; intros ;  clear H ; subst. simpl.
    rewrite beq_Attribute_refl.
    congruence.

  - apply IHmodelLinks in H.
    
    match goal with [ |- context[ if ?P then _ else _ ]  ] => destruct P eqn:? end .
    congruence.
    assumption.
Qed. 

(* Used *)
Corollary getAttributeType_In_left_2 att t (m:Model ClassMM): 
  In (AttributeTypeLink {| source_attribute := att ; a_type := t |}) m.(modelLinks) ->
  exists r, getAttributeType att m = Some r.
Proof.
  intro H.
  apply getAttributeType_In_left in H.
  destruct (getAttributeType att m).
  + eauto.
  + contradiction.
Qed.


(** * Well formed models (definitions) *)


(* Not Used *)
Definition wf_classmodel_nodup (cm:ClassModel) : Prop :=
   List.NoDup cm.(modelElements).


(** Unique identifiers (classes) *)
(* Not Used *)
Definition wf_classmodel_unique_class_id (cm:ClassModel) : Prop :=
  forall c1 c2,
  In (ClassElement c1) cm.(modelElements) ->
  In (ClassElement c2) cm.(modelElements) ->
          c1 <> c2 ->
          c1.(class_id) <> c2.(class_id).


(** Two different classes have different names. *)
(* Not Used *)
Definition wf_classmodel_unique_class_names (cm:ClassModel) :=
  forall i1 i2 n1 n2,
  In (ClassElement {| class_id := i1 ; class_name := n1 |}) cm.(modelElements) ->
  In (ClassElement {| class_id := i2 ; class_name := n2 |}) cm.(modelElements) ->
          i1 <> i2 ->
          n1 <> n2.
(** Remark : the class name could be used as a unique identifier. *)


(** An attribute (of a class) has only one type (encoded in the links). *)
(* Used *)
Definition wf_classmodel_unique_attribute_types (cm:ClassModel) :=
  forall attr c1 c2,
  In (AttributeTypeLink {| source_attribute := attr ; a_type := c1 |}) cm.(modelLinks) ->
  In (AttributeTypeLink {| source_attribute := attr ; a_type := c2 |}) cm.(modelLinks) ->
          c1 = c2. 
(** Reminder : If two attributes of different classes have the same name, they will have different identifiers are so they are different with respect to = and <> *)
(** Remark : Above, nothing forces c1/c2 to be in cm.(modelElements). See below for such a constraint.  *)

(** The attributes of each class are defined in a single link ClassAttributeLink (and not by small bits). *)
(* Not Used *)
Definition wf_classmodel_unique_attribute_link (cm:ClassModel) :=
  forall a1 a2,
  In (ClassAttributeLink a1) cm.(modelLinks) ->
  In (ClassAttributeLink a2) cm.(modelLinks) ->
  a1 <> a2 ->
  a1.(source_class) <> a2.(source_class).


(** A class does not contains two times the same attribute (same name and identifier) *)
(* Not Used. *)
Definition wf_classmodel_unique_attribute_per_class (cm:ClassModel) :=
  forall c l a1 a2,
  In (ClassAttributeLink {| source_class := c ; attrs := l |}) cm.(modelLinks) ->
  In a1 l ->
  In a2 l ->
  a1 <> a2 ->
  a1.(attr_id) <> a2.(attr_id) /\ a1.(attr_name) <> a2.(attr_name).


(** Remark : We can have several attributes with the same name (attached to different classes). *)


(* Used *)
Definition wf_classmodel_types_exist (cm:ClassModel) :=
  forall attr c,
    In (AttributeTypeLink {| source_attribute := attr ; a_type := c |}) cm.(modelLinks)  ->
    In (ClassElement c) cm.(modelElements).


(** * Results on well-formed models *)

(* Used *)    
Lemma getAttributeType_classex_right cm :
  wf_classmodel_types_exist cm ->
  forall att r, 
    getAttributeType att cm = Some r ->
    In (ClassElement r) cm.(modelElements).
Proof.
  intro WF ; intros.
  unfold wf_classmodel_types_exist in WF.
  eapply WF.
  apply getAttributeType_In_right  in H ; []. 
  exact H.
Qed.


(* Used *)
Lemma getAttributeType_In_left_3 att t (m:Model ClassMM): 
  wf_classmodel_unique_attribute_types m ->
  In (AttributeTypeLink {| source_attribute := att ; a_type := t |}) m.(modelLinks) ->
  getAttributeType att m = Some t.
Proof.

  intros WF H.
  Tactics.duplicate H G.
  apply getAttributeType_In_left in G.
  destruct (getAttributeType att m) eqn:E ; [ clear G | contradiction ].
  apply getAttributeType_In_right in E.

  f_equal.
  
  eapply WF ; eassumption.
Qed.
 
