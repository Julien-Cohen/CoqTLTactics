Require Import String.
Require Import Bool.
Require Import List.      (* sequence *)
Require Import PeanoNat.
Require Import EqNat.
Require Import Coq.Logic.Eqdep_dec.


Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.utils.CpdtTactics.
Require        core.Tactics.

(** Base types for elements *)

Record Class_t := { class_id : nat ; class_name : string }.

Record Attribute_t := { attr_id : nat ; derived : bool ; attr_name : string }.

(** Base types for links *)

Record ClassAttributes_t := { source_class : Class_t ; attrs : list Attribute_t }.

Record AttributeType_t := { source_attribute : Attribute_t ; a_type : Class_t }.


(* Equality *)

Definition beq_Class (c1 : Class_t) (c2 : Class_t) : bool :=
  beq_nat (class_id c1) (class_id c2) && beq_string (class_name c1) (class_name c2).

Definition beq_Attribute (a1 : Attribute_t) (a2 : Attribute_t) : bool :=
  beq_nat (attr_id a1) (attr_id a2) && eqb (derived a1) (derived a2) && beq_string (attr_name a1) (attr_name a2).

Definition beq_AttributeType (c1 : AttributeType_t) (c2 : AttributeType_t) : bool :=
  beq_Attribute (source_attribute c1) (source_attribute c2) && beq_Class (a_type c1) (a_type c2).

Definition beq_ClassAttributes (c1 : ClassAttributes_t) (c2 : ClassAttributes_t) : bool :=
  beq_Class (source_class c1) (source_class c2) && list_beq beq_Attribute (attrs c1) (attrs c2).


Lemma lem_beq_Class_id:
 forall (a1 a2: Class_t),
   beq_Class a1 a2 = true -> a1 = a2.
Proof.
  Tactics.beq_eq_tac.
Qed.

Lemma beq_Class_refl : 
  forall t, beq_Class t t = true.
Proof.
  destruct t. unfold beq_Class. simpl.
  rewrite Nat.eqb_refl.
  rewrite lem_beq_string_id.
  reflexivity.
Qed. 

Lemma lem_beq_Attribute_id:
 forall (a1 a2: Attribute_t),
   beq_Attribute a1 a2 = true -> a1 = a2.
Proof.
  Tactics.beq_eq_tac.
Qed.

Lemma lem_beq_AttributeType_id:
 forall a1 a2,
   beq_AttributeType a1 a2 = true -> a1 = a2.
Proof.
  Tactics.beq_eq_tac.
Qed.

Hint Resolve lem_beq_Attribute_id : beq_eq_database.
(* this is necessary for the success of the [beq_eq_tac] tactics in the lemma below *)

Lemma lem_beq_ClassAttributes_id:
 forall a1 a2,
   beq_ClassAttributes a1 a2 = true -> a1 = a2.
Proof.
  Tactics.beq_eq_tac.
Qed.


(** Data types (to build models) *)

Inductive Element : Set :=
  ClassElement : Class_t -> Element
| AttributeElement : Attribute_t -> Element.

Definition beq_Element (c1 : Element) (c2 : Element) : bool :=
  match c1, c2 with
  | ClassElement o1, ClassElement o2 => beq_Class o1 o2
  | AttributeElement o1, AttributeElement o2 => beq_Attribute o1 o2
  | _, _ => false
  end.


Inductive Link : Set :=
   | ClassAttributeLink : ClassAttributes_t -> Link
   | AttributeTypeLink : AttributeType_t -> Link.

Definition beq_Link (c1 : Link) (c2 : Link) : bool :=
  match c1, c2 with
  | ClassAttributeLink o1, ClassAttributeLink o2 => beq_ClassAttributes o1 o2
  | AttributeTypeLink o1, AttributeTypeLink o2 => beq_AttributeType o1 o2
  | _, _ => false
  end.


(** Meta-types (or kinds, to be used in rules) *)

Inductive ElementKind : Set :=
  Class_K | Attribute_K.

Inductive LinkKind : Set :=
  ClassAttribute_K | AttributeType_K.


Lemma eqEKind_dec : forall (c1:ElementKind) (c2:ElementKind), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Lemma eqLKind_dec : forall (c1:LinkKind) (c2:LinkKind), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

(** Reflective functions (typing : correspondence between abstract types (kinds) and model data) *)


Definition getTypeByEKind (k : ElementKind) : Set :=
  match k with
  | Class_K => Class_t
  | Attribute_K => Attribute_t
  end.

Definition lift_EKind k : (getTypeByEKind k) -> Element := 
  match k with 
  | Class_K => ClassElement 
  | Attribute_K => AttributeElement 
  end.

Definition get_E_data (k : ElementKind) (c : Element) : option (getTypeByEKind k) :=
  match (k,c) as e return (option (getTypeByEKind (fst e))) with
  | (Class_K , ClassElement v) => Some v 
  | (Attribute_K, AttributeElement v) => Some v 
  | (_ , _) => None
  end.


Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with
  | ClassAttribute_K => ClassAttributes_t
  | AttributeType_K => AttributeType_t
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | ClassAttribute_K => ClassAttributeLink
  | AttributeType_K => AttributeTypeLink
  end.



Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (ClassAttribute_K , ClassAttributeLink v) => Some v 
  | (AttributeType_K, AttributeTypeLink v) => Some v 
  | (_ , _) => None 
  end.


(* Typeclass Instance *)

Definition ClassMM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eqdec := beq_Element ;
  links_eqdec := beq_Link
|}.


#[export]
Instance ClassElementDenotation : Denotation Element ElementKind :=
{
  denoteDatatype := getTypeByEKind;
  unbox := get_E_data;
  constructor := lift_EKind;
}.


#[export]
Instance ClassLinkDenotation : Denotation Link LinkKind :=
{
  denoteDatatype := getTypeByLKind;
  unbox := get_L_data;
  constructor := lift_LKind;
}.


#[export]
Instance ClassMetamodel : ModelingMetamodel ClassMM :=
{ 
    elements := ClassElementDenotation;
    links := ClassLinkDenotation; 
}.

Definition ClassModel := Model ClassMM.



(** General functions (used in transformations) *)


Definition getId (c : Element) : nat :=
  match c with
  | ClassElement c => c.(class_id)
  | AttributeElement a => a.(attr_id)
  end.

Definition getName (c : Element) : string :=
  match c with
  | ClassElement c => c.(class_name)
  | AttributeElement a => a.(attr_name)
  end.

Fixpoint getClassAttributesOnLinks (c : Class_t) (l : list Link) : option (list Attribute_t) :=
  match l with
  | (ClassAttributeLink c1) :: l1 => 
      if beq_Class c1.(source_class) c 
      then Some c1.(attrs) 
      else getClassAttributesOnLinks c l1
  | _ :: l1 => getClassAttributesOnLinks c l1
  | nil => None
  end.



Definition getClassAttributes (c : Class_t) (m : ClassModel) : option (list Attribute_t) :=
  getClassAttributesOnLinks c m.(modelLinks).

Definition getClassAttributesElements (c : Class_t) (m : ClassModel) : option (list Element) :=
  match getClassAttributes c m with
  | Some l => Some (map AttributeElement l)
  | None => None
  end.

Fixpoint getAttributeTypeOnLinks (a : Attribute_t) (l : list Link) : option Class_t :=
  match l with
  | (AttributeTypeLink a1) :: l1 => 
      if beq_Attribute a1.(source_attribute) a 
      then Some a1.(a_type) 
      else getAttributeTypeOnLinks a l1
  | _ :: l1 => getAttributeTypeOnLinks a l1
  | nil => None
  end.

Definition getAttributeType (a : Attribute_t) (m : ClassModel) : option Class_t :=
  getAttributeTypeOnLinks a m.(modelLinks).


Definition getAttributeTypeElement (a : Attribute_t) (m : ClassModel) : option Element :=
  match getAttributeType a m with
  | Some c => Some (ClassElement c)
  | None => None
  end.

Definition defaultInstanceOfClass (c: ElementKind) : (getTypeByEKind c) :=
  match c with
  | Class_K => (Build_Class_t 0 "")
  | Attribute_K => (Build_Attribute_t 0 false "")
  end.




(** Useful lemmas *)

Lemma Class_invert : 
  forall (k: ElementKind) (t1 t2: getTypeByEKind k), 
    constructor k t1 = constructor k t2 ->
    t1 = t2.
Proof.
  intros. destruct k ; simpl in * ; congruence.
Qed.



Lemma Element_dec: 
  forall (a: Element),
    (instanceof Class_K a) = true
 \/ (instanceof Attribute_K a) = true.
Proof.

  intro.
  destruct a ; unfold instanceof ; simpl ; auto.
Qed.

Lemma Class_Element_cast:
  forall a c,
    unbox Class_K a = return c ->
      ClassElement c = a.
Proof.
  unfold unbox ; simpl. 
  unfold get_E_data.
  intros ; destruct a ; congruence.
Qed.

Lemma Attribute_Element_cast:
  forall a c,
    unbox Attribute_K a = return c ->
      AttributeElement c = a.
Proof.
  unfold unbox ; simpl.
  unfold get_E_data.
  intros ; destruct a ; congruence.
Qed.

Lemma Class_dec :
  forall x y : Class_t, {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply String.string_dec.
  - apply Nat.eq_dec.
Qed.

Lemma Attribute_dec :
  forall x y : Attribute_t, {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply String.string_dec.
  - apply Bool.bool_dec.
  - apply Nat.eq_dec.
Qed.

Lemma eq_dec : forall (x y : Element), {x = y} + {x <> y}.
  intros ; destruct x, y ; try (right; discriminate).
  - destruct (Class_dec c c0).
    + left. congruence.
    + right. congruence. 
  - destruct (Attribute_dec a a0).
    + left. congruence.
    + right. congruence.
Qed.
