(** Imports Native *)
Require Import String.
Require Import Bool.
Require Import List.
Require Import PeanoNat.
Require Import EqNat.
Require Import Coq.Logic.Eqdep_dec.

(** Imports CoqTL *)
Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.utils.CpdtTactics.
Require        core.Tactics.

(** Base types for elements *)
Record Class_t := { Class_id : nat ; Class_name : string }.
Scheme Equality for Class_t.
Lemma lem_Class_t_beq_id : forall (e1 e2 : Class_t), Class_t_beq e1 e2 = true -> e1 = e2.
Proof. exact internal_Class_t_dec_bl. Qed. 
Lemma lem_Class_t_beq_refl : forall (e : Class_t), Class_t_beq e e = true.
Proof. intro ; apply internal_Class_t_dec_lb ; auto. Qed. 


Record Attribute_t := { Attribute_id : nat ; Attribute_derived : bool ; Attribute_name : string }.
Scheme Equality for Attribute_t.
Lemma lem_Attribute_t_beq_id : forall (e1 e2 : Attribute_t), Attribute_t_beq e1 e2 = true -> e1 = e2.
Proof. exact internal_Attribute_t_dec_bl. Qed. 
Lemma lem_Attribute_t_beq_refl : forall (e : Attribute_t), Attribute_t_beq e e = true.
Proof. intro ; apply internal_Attribute_t_dec_lb ; auto. Qed. 



(** Base types for links *)
Record Class_attributes_t := { Class_attributes_t_source : Class_t ; Class_attributes_t_target : list Attribute_t }.
(*Scheme Equality for Class_attributes_t. ==Does not work== *)
Definition Class_attributes_t_beq (a1 a2: Class_attributes_t) : bool := 
  Class_t_beq a1.(Class_attributes_t_source) a2.(Class_attributes_t_source) && list_beq Attribute_t_beq a1.(Class_attributes_t_target) a2.(Class_attributes_t_target).
Lemma lem_Class_attributes_t_beq_id : forall (e1 e2 : Class_attributes_t), Class_attributes_t_beq e1 e2 = true -> e1 = e2.
Proof. Admitted. 
Lemma lem_Class_attributes_t_beq_refl : forall (e : Class_attributes_t), Class_attributes_t_beq e e = true.
Proof. Admitted. 


Record Attribute_type_t := { Attribute_type_t_source : Attribute_t ; Attribute_type_t_target : Class_t }.
Scheme Equality for Attribute_type_t.
Lemma lem_Attribute_type_t_beq_id : forall (e1 e2 : Attribute_type_t), Attribute_type_t_beq e1 e2 = true -> e1 = e2.
Proof. exact internal_Attribute_type_t_dec_bl. Qed.
Lemma lem_Attribute_type_t_beq_refl : forall (e : Attribute_type_t), Attribute_type_t_beq e e = true.
Proof. intro ; apply internal_Attribute_type_t_dec_lb ; auto. Qed. 



(** Data types for element (to build models) *)
Inductive Element : Set :=
  | ClassElement : Class_t -> Element
  | AttributeElement : Attribute_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  | Class_attributesLink : Class_attributes_t -> Link
  | Attribute_typeLink : Attribute_type_t -> Link
.
(*Scheme Equality for Link. ==Does not work== *)

Definition Link_beq (c1 : Link) (c2 : Link) : bool :=
  match c1, c2 with
  | Class_attributesLink o1, Class_attributesLink o2 => Class_attributes_t_beq o1 o2
  | Attribute_typeLink o1, Attribute_typeLink o2 => Attribute_type_t_beq o1 o2
  | _, _ => false
  end.

(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
  | Class_K
  | Attribute_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
  | Class_attributes_K
  | Attribute_type_K
.
Scheme Equality for LinkKind.

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
  | (Class_K, ClassElement v)  => Some v
  | (Attribute_K, AttributeElement v)  => Some v
  | (_ , _) => None
  end.


Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with
  | Class_attributes_K => Class_attributes_t
  | Attribute_type_K => Attribute_type_t
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | Class_attributes_K => Class_attributesLink
  | Attribute_type_K => Attribute_typeLink
  end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (Class_attributes_K, Class_attributesLink v)  => Some v
  | (Attribute_type_K, Attribute_typeLink v)  => Some v
  | (_ , _) => None
  end.

(** Typeclass Instance *)
Definition MM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eqdec := Element_beq ;
  links_eqdec := Link_beq
|}.


#[export]
Instance ClassElementDenotation : Denotation Element ElementKind :=
{
  denoteDatatype := getTypeByEKind ;
  unbox := get_E_data ;
  constructor := lift_EKind ;
}.


#[export]
Instance ClassLinkDenotation : Denotation Link LinkKind :=
{
  denoteDatatype := getTypeByLKind ;
  unbox := get_L_data ;
  constructor := lift_LKind ;
}.


#[export]
Instance MMM : ModelingMetamodel MM :=
{
  elements := ClassElementDenotation ;
  links := ClassLinkDenotation ;
}.


Definition ClassModel := Model MM.

(** General functions (used in transformations) *)
Fixpoint getClass_attributesOnLinks (c : Class_t) (l : list Link) : option (list Attribute_t) :=
 match l with
  | (Class_attributesLink x) :: l1 =>
    if Class_t_beq x.(Class_attributes_t_source) c
      then (Some x.(Class_attributes_t_target))
      else getClass_attributesOnLinks c l1
  | _ :: l1 => getClass_attributesOnLinks c l1
  | nil => None
 end.


Definition getClass_attributes (c : Class_t) (m : ClassModel) : option (list Attribute_t) :=
  getClass_attributesOnLinks c m.(modelLinks).


Fixpoint getAttribute_typeOnLinks (a : Attribute_t) (l : list Link) : option (Class_t) :=
 match l with
  | (Attribute_typeLink x) :: l1 =>
    if Attribute_t_beq x.(Attribute_type_t_source) a
      then (Some x.(Attribute_type_t_target))
      else getAttribute_typeOnLinks a l1
  | _ :: l1 => getAttribute_typeOnLinks a l1
  | nil => None
 end.


Definition getAttribute_type (a : Attribute_t) (m : ClassModel) : option Class_t :=
  getAttribute_typeOnLinks a m.(modelLinks).



(** Useful lemmas *)
Lemma Class_invert : 
  forall (k: ElementKind) (t1 t2: getTypeByEKind k),
    constructor k t1 = constructor k t2 -> t1 = t2.
Proof. intro k ; destruct k ; simpl; congruence.  Qed. 


Lemma Element_dec : 
  forall (a: Element),
(instanceof Class_K a) = true\/(instanceof Attribute_K a) = true
.
Proof. destruct a ; auto. Qed. 


Lemma ClassElement_cast :
  forall x y,
    unbox Class_K x = return y -> ClassElement y = x.
Proof. destruct x ; destruct y ; compute ; congruence. Qed. 


Lemma AttributeElement_cast :
  forall x y,
    unbox Attribute_K x = return y -> AttributeElement y = x.
Proof. destruct x ; destruct y ; compute ; congruence. Qed. 

(** Manual addition *)
Definition getClass_attributesElements (c : Class_t) (m : ClassModel) : option (list Element) :=
  match getClass_attributes c m with
  | Some l => Some (map AttributeElement l)
  | None => None
  end.

Definition getAttribute_typeElement (a : Attribute_t) (m : ClassModel) : option Element :=
  option_map ClassElement (getAttribute_type a m).

Ltac inv_getAttribute_typeElement H :=
   match type of H with 
     getAttribute_typeElement _ _ = Some _ =>
       unfold getAttribute_typeElement in H ;
       OptionUtils.monadInv H
   end.


Definition defaultInstanceOfClass (c: ElementKind) : (getTypeByEKind c) :=
  match c with
  | Class_K => (Build_Class_t 0 "")
  | Attribute_K => (Build_Attribute_t 0 false "")
  end.


Definition getId (c : Element) : nat :=
  match c with
  | ClassElement c => c.(Class_id)
  | AttributeElement a => a.(Attribute_id)
  end.

Definition getName (c : Element) : string :=
  match c with
  | ClassElement c => c.(Class_name)
  | AttributeElement a => a.(Attribute_name)
  end.

