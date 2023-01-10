
Require Import List.

Require Import core.utils.Utils.
Require Import core.Model.

Require Import transformations.Class2Relational.ClassMetamodel.

From transformations.Class2Relational Require Tactics.


Lemma get_in l t v : 
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


(* FIXME : not used anymore. *)
Corollary getAttributeType_In_right att m t: 
  getAttributeType att m = Some t ->
    In (AttributeTypeLink {| source_attribute := att ; a_type := t |}) m.(modelLinks).
Proof.
  unfold getAttributeType.
  apply get_in. 
Qed. 

(* not used *)
Remark getAttributeType_In_left att t (m:Model ClassMM): 
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


(** *** Well formed models. *)

(* Probablement pas necessaire. *)
Definition wf_classmodel_nodup (cm:ClassModel) : Prop :=
   List.NoDup cm.(modelElements).

(* identifiants uniques (classes) *)
Definition wf_classmodel_unique_class_id (cm:ClassModel) : Prop :=
  forall c1 c2,
  In (ClassElement c1) cm.(modelElements) ->
  In (ClassElement c2) cm.(modelElements) ->
          c1 <> c2 ->
          c1.(class_id) <> c2.(class_id).

(* Deux classes différentes ont des noms différents. *)
Definition wf_classmodel_unique_class_names (cm:ClassModel) :=
  forall i1 i2 n1 n2,
  In (ClassElement {| class_id := i1 ; class_name := n1 |}) cm.(modelElements) ->
  In (ClassElement {| class_id := i2 ; class_name := n2 |}) cm.(modelElements) ->
          i1 <> i2 ->
          n1 <> n2.
(* Remarque : le nom de classe pourrait servir d'identifiant unique. *)


(* Un attribut (d'une classe) n'a qu'un type (encodé dans les liens). *)
Definition wf_classmodel_unique_attribute_types (cm:ClassModel) :=
  forall attr c1 c2,
  In (AttributeTypeLink {| source_attribute := attr ; a_type := c1 |}) cm.(modelLinks) ->
  In (AttributeTypeLink {| source_attribute := attr ; a_type := c2 |}) cm.(modelLinks) ->
          c1 = c2. 
(* Rappel : Si deux attributs de classes différentes ont le même nom, ils auront des id différents et sont donc diffrent au sens de = / <> *)
(* Remarque : ci-dessus rien ne contraint c1/c2 à être dans cm.(modelElements). Voir ci-dessous pour une telle contrainte.  *)

(* Les attributs de chaque classe sont définis dans un seul lien ClassAttributeLink (et pas par petits bouts) *)
Definition wf_classmodel_unique_attribute_link (cm:ClassModel) :=
  forall a1 a2,
  In (ClassAttributeLink a1) cm.(modelLinks) ->
  In (ClassAttributeLink a2) cm.(modelLinks) ->
  a1 <> a2 ->
  a1.(source_class) <> a2.(source_class).

(* une classe n'a pas deux fois le même attribut (le nom et l'identifiant doivent être différents) *)
Definition wf_classmodel_unique_attribute_per_class (cm:ClassModel) :=
  forall c l a1 a2,
  In (ClassAttributeLink {| source_class := c ; attrs := l |}) cm.(modelLinks) ->
  In a1 l ->
  In a2 l ->
  a1 <> a2 ->
  a1.(attr_id) <> a2.(attr_id) /\ a1.(attr_name) <> a2.(attr_name).

(** Remarque : On peut avoir plusieurs attributs de même nom (attachés à des classes différentes). *)

Definition wf_classmodel_types_exist (cm:ClassModel) :=
  forall attr c,
    In (AttributeTypeLink {| source_attribute := attr ; a_type := c |}) cm.(modelLinks)  ->
    In (ClassElement c) cm.(modelElements).

    
Lemma get_ex cm :
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
