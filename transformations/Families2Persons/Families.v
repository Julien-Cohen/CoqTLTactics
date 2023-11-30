(** Imports Native *)
Require Import String.
Require Import Bool.
Require Import List.
Require Import PeanoNat.
Require Import EqNat.

(** Imports CoqTL *)
Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

(** Base types for elements *)
Record Family_t := { Family_lastName : string }.
Scheme Equality for Family_t.


Record Member_t := { Member_firstName : string }.
Scheme Equality for Member_t.



(** Base types for links *)
Record Family_ffather_t := { Family_ffather_t_lglue : Family_t ; Family_ffather_t_rglue : Member_t }.


Record Family_fmother_t := { Family_fmother_t_lglue : Family_t ; Family_fmother_t_rglue : Member_t }.


Record Family_fsons_t := { Family_fsons_t_lglue : Family_t ; Family_fsons_t_rglue : list Member_t }.


Record Family_fdaughters_t := { Family_fdaughters_t_lglue : Family_t ; Family_fdaughters_t_rglue : list Member_t }.


Record Member_familyFather_t := { Member_familyFather_t_lglue : Member_t ; Member_familyFather_t_rglue : Family_t }.


Record Member_familyMother_t := { Member_familyMother_t_lglue : Member_t ; Member_familyMother_t_rglue : Family_t }.


Record Member_familySon_t := { Member_familySon_t_lglue : Member_t ; Member_familySon_t_rglue : Family_t }.


Record Member_familyDaughter_t := { Member_familyDaughter_t_lglue : Member_t ; Member_familyDaughter_t_rglue : Family_t }.



(** Data types for element (to build models) *)
Inductive Element : Set :=
  | FamilyElement : Family_t -> Element
  | MemberElement : Member_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  | Family_ffatherLink : Family_ffather_t -> Link
  | Family_fmotherLink : Family_fmother_t -> Link
  | Family_fsonsLink : Family_fsons_t -> Link
  | Family_fdaughtersLink : Family_fdaughters_t -> Link
  | Member_familyFatherLink : Member_familyFather_t -> Link
  | Member_familyMotherLink : Member_familyMother_t -> Link
  | Member_familySonLink : Member_familySon_t -> Link
  | Member_familyDaughterLink : Member_familyDaughter_t -> Link
.

(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
  | Family_K
  | Member_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
  | Family_ffather_K
  | Family_fmother_K
  | Family_fsons_K
  | Family_fdaughters_K
  | Member_familyFather_K
  | Member_familyMother_K
  | Member_familySon_K
  | Member_familyDaughter_K
.
Scheme Equality for LinkKind.

(** Reflective functions (typing : correspondence between abstract types (kinds) and model data) *)
Definition getTypeByEKind (k : ElementKind) : Set :=
  match k with
  | Family_K => Family_t
  | Member_K => Member_t
  end.


Definition lift_EKind k : (getTypeByEKind k) -> Element := 
  match k with
  | Family_K => FamilyElement
  | Member_K => MemberElement
  end.


Definition get_E_data (k : ElementKind) (c : Element) : option (getTypeByEKind k) :=
  match (k,c) as e return (option (getTypeByEKind (fst e))) with
  | (Family_K, FamilyElement v)  => Some v
  | (Member_K, MemberElement v)  => Some v
  | (_ , _) => None
  end.


Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with
  | Family_ffather_K => Family_ffather_t
  | Family_fmother_K => Family_fmother_t
  | Family_fsons_K => Family_fsons_t
  | Family_fdaughters_K => Family_fdaughters_t
  | Member_familyFather_K => Member_familyFather_t
  | Member_familyMother_K => Member_familyMother_t
  | Member_familySon_K => Member_familySon_t
  | Member_familyDaughter_K => Member_familyDaughter_t
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | Family_ffather_K => Family_ffatherLink
  | Family_fmother_K => Family_fmotherLink
  | Family_fsons_K => Family_fsonsLink
  | Family_fdaughters_K => Family_fdaughtersLink
  | Member_familyFather_K => Member_familyFatherLink
  | Member_familyMother_K => Member_familyMotherLink
  | Member_familySon_K => Member_familySonLink
  | Member_familyDaughter_K => Member_familyDaughterLink
  end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (Family_ffather_K, Family_ffatherLink v)  => Some v
  | (Family_fmother_K, Family_fmotherLink v)  => Some v
  | (Family_fsons_K, Family_fsonsLink v)  => Some v
  | (Family_fdaughters_K, Family_fdaughtersLink v)  => Some v
  | (Member_familyFather_K, Member_familyFatherLink v)  => Some v
  | (Member_familyMother_K, Member_familyMotherLink v)  => Some v
  | (Member_familySon_K, Member_familySonLink v)  => Some v
  | (Member_familyDaughter_K, Member_familyDaughterLink v)  => Some v
  | (_ , _) => None
  end.

(** Typeclass Instance *)
Definition MM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eq_dec := Element_eq_dec ;
|}.


#[export]
Instance FamiliesElementDenotation : Denotation Element ElementKind :=
{
  denoteDatatype := getTypeByEKind ;
  unbox := get_E_data ;
  constructor := lift_EKind ;
}.


#[export]
Instance FamiliesLinkDenotation : Denotation Link LinkKind :=
{
  denoteDatatype := getTypeByLKind ;
  unbox := get_L_data ;
  constructor := lift_LKind ;
}.


#[export]
Instance MMM : ModelingMetamodel MM :=
{
  elements := FamiliesElementDenotation ;
  links := FamiliesLinkDenotation ;
}.


Definition M := Model MM.

(** General functions (used in transformations) *)
Fixpoint getFamily_ffatherOnLinks (f : Family_t) (l : list Link) : option (Member_t) :=
 match l with
  | (Family_ffatherLink x) :: l1 =>
    if Family_t_beq x.(Family_ffather_t_lglue) f
      then (Some x.(Family_ffather_t_rglue))
      else getFamily_ffatherOnLinks f l1
  | _ :: l1 => getFamily_ffatherOnLinks f l1
  | nil => None
 end.


Definition getFamily_ffather (m : M) (f : Family_t) : option (Member_t) :=
  getFamily_ffatherOnLinks f m.(modelLinks).


Fixpoint getFamily_fmotherOnLinks (f : Family_t) (l : list Link) : option (Member_t) :=
 match l with
  | (Family_fmotherLink x) :: l1 =>
    if Family_t_beq x.(Family_fmother_t_lglue) f
      then (Some x.(Family_fmother_t_rglue))
      else getFamily_fmotherOnLinks f l1
  | _ :: l1 => getFamily_fmotherOnLinks f l1
  | nil => None
 end.


Definition getFamily_fmother (m : M) (f : Family_t) : option (Member_t) :=
  getFamily_fmotherOnLinks f m.(modelLinks).


Fixpoint getFamily_fsonsOnLinks (f : Family_t) (l : list Link) : option (list Member_t) :=
 match l with
  | (Family_fsonsLink x) :: l1 =>
    if Family_t_beq x.(Family_fsons_t_lglue) f
      then (Some x.(Family_fsons_t_rglue))
      else getFamily_fsonsOnLinks f l1
  | _ :: l1 => getFamily_fsonsOnLinks f l1
  | nil => None
 end.


Definition getFamily_fsons (m : M) (f : Family_t) : option (list Member_t) :=
  getFamily_fsonsOnLinks f m.(modelLinks).


Fixpoint getFamily_fdaughtersOnLinks (f : Family_t) (l : list Link) : option (list Member_t) :=
 match l with
  | (Family_fdaughtersLink x) :: l1 =>
    if Family_t_beq x.(Family_fdaughters_t_lglue) f
      then (Some x.(Family_fdaughters_t_rglue))
      else getFamily_fdaughtersOnLinks f l1
  | _ :: l1 => getFamily_fdaughtersOnLinks f l1
  | nil => None
 end.


Definition getFamily_fdaughters (m : M) (f : Family_t) : option (list Member_t) :=
  getFamily_fdaughtersOnLinks f m.(modelLinks).


Fixpoint getMember_familyFatherOnLinks (m : Member_t) (l : list Link) : option (Family_t) :=
 match l with
  | (Member_familyFatherLink x) :: l1 =>
    if Member_t_beq x.(Member_familyFather_t_lglue) m
      then (Some x.(Member_familyFather_t_rglue))
      else getMember_familyFatherOnLinks m l1
  | _ :: l1 => getMember_familyFatherOnLinks m l1
  | nil => None
 end.


Definition getMember_familyFather (_m : M) (m : Member_t) : option (Family_t) :=
  getMember_familyFatherOnLinks m _m.(modelLinks).


Fixpoint getMember_familyMotherOnLinks (m : Member_t) (l : list Link) : option (Family_t) :=
 match l with
  | (Member_familyMotherLink x) :: l1 =>
    if Member_t_beq x.(Member_familyMother_t_lglue) m
      then (Some x.(Member_familyMother_t_rglue))
      else getMember_familyMotherOnLinks m l1
  | _ :: l1 => getMember_familyMotherOnLinks m l1
  | nil => None
 end.


Definition getMember_familyMother (_m : M) (m : Member_t) : option (Family_t) :=
  getMember_familyMotherOnLinks m _m.(modelLinks).


Fixpoint getMember_familySonOnLinks (m : Member_t) (l : list Link) : option (Family_t) :=
 match l with
  | (Member_familySonLink x) :: l1 =>
    if Member_t_beq x.(Member_familySon_t_lglue) m
      then (Some x.(Member_familySon_t_rglue))
      else getMember_familySonOnLinks m l1
  | _ :: l1 => getMember_familySonOnLinks m l1
  | nil => None
 end.


Definition getMember_familySon (_m : M) (m : Member_t) : option (Family_t) :=
  getMember_familySonOnLinks m _m.(modelLinks).


Fixpoint getMember_familyDaughterOnLinks (m : Member_t) (l : list Link) : option (Family_t) :=
 match l with
  | (Member_familyDaughterLink x) :: l1 =>
    if Member_t_beq x.(Member_familyDaughter_t_lglue) m
      then (Some x.(Member_familyDaughter_t_rglue))
      else getMember_familyDaughterOnLinks m l1
  | _ :: l1 => getMember_familyDaughterOnLinks m l1
  | nil => None
 end.


Definition getMember_familyDaughter (_m : M) (m : Member_t) : option (Family_t) :=
  getMember_familyDaughterOnLinks m _m.(modelLinks).



