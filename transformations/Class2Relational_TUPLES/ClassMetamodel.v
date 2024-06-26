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

Require Import Glue.

(** Base types for elements *)

Record Class_t := { class_id : nat ; class_name : string }.

Scheme Equality for Class_t.

Record Attribute_t := { attr_id : nat ; derived : bool ; attr_name : string }.

Scheme Equality for Attribute_t.

(** Base types for links *)

Notation ClassAttributes_glue := (Glue Class_t (list Attribute_t)).

Notation AttributeType_glue := (Glue Attribute_t Class_t).




(** Data types (to build models) *)

Inductive Element : Set :=
  ClassElement : Class_t -> Element
| AttributeElement : Attribute_t -> Element.

Scheme Equality for Element.


Inductive Link : Set :=
   | ClassAttributeLink : ClassAttributes_glue -> Link
   | AttributeTypeLink : AttributeType_glue -> Link.


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
  | ClassAttribute_K => ClassAttributes_glue
  | AttributeType_K => AttributeType_glue
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
  elements_eq_dec := Element_eq_dec ;
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
      if Class_t_beq c1.(src) c 
      then Some c1.(trg) 
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
      if Attribute_t_beq a1.(src) a 
      then Some a1.(trg) 
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



