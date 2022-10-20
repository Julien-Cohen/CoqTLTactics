Require Import String.
Require Import Bool.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import PeanoNat.
Require Import EqNat.
Require Import Coq.Logic.Eqdep_dec.

Require Import core.EqDec.
Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.utils.CpdtTactics.
(* Base types *)

Record Class := { class_id : nat ; class_name : string }.

Record Attribute := { attr_id : nat ; derived : bool ; attr_name : string }.

Record ClassAttributes := { in_class : Class ; attrs : list Attribute }.

Record AttributeType := { for_attribute : Attribute ; type : Class }.

(* Accessors *)

Definition beq_Class (c1 : Class) (c2 : Class) : bool :=
  beq_nat (class_id c1) (class_id c2) && beq_string (class_name c1) (class_name c2).

Definition beq_Attribute (a1 : Attribute) (a2 : Attribute) : bool :=
  beq_nat (attr_id a1) (attr_id a2) && eqb (derived a1) (derived a2) && beq_string (attr_name a1) (attr_name a2).

Lemma lem_beq_Class_id:
 forall (a1 a2: Class),
   beq_Class a1 a2 = true -> a1 = a2.
Proof.
intros.
unfold beq_Class in H.
unfold "&&" in H.
destruct (class_id a1 =? class_id a2) eqn: ca1.
- apply (lem_beq_string_eq2) in H.
  apply (beq_nat_true) in ca1.
  destruct a1,a2.
  simpl in ca1, H.
  rewrite ca1,H.
  auto.
- congruence.
Qed.

Lemma lem_beq_Attribute_id:
 forall (a1 a2: Attribute),
   beq_Attribute a1 a2 = true -> a1 = a2.
Proof.
intros.
unfold beq_Attribute in H.
unfold "&&" in H.
destruct (attr_id a1 =? attr_id a2) eqn: ca1.
- destruct (eqb (derived a1) (derived a2)) eqn: ca2.
  + apply (lem_beq_string_eq2) in H.
    apply (beq_nat_true) in ca1.
    apply (eqb_prop) in ca2.
    destruct a1,a2.
    simpl in ca1,ca2, H.
    rewrite ca1,ca2,H.
    auto.
  + congruence. 
- congruence.
Qed.



(* Meta-types *)

Inductive Classes : Set :=
  ClassClass | AttributeClass.

Definition getTypeByClass (type : Classes) : Set :=
  match type with
  | ClassClass => Class
  | AttributeClass => Attribute
  end.

(* not used *)
Definition getEAttributeTypesByClass (c: Classes): Set :=
  match c with
  | ClassClass => (nat * string)
  | AttributeClass => (nat * bool * string)
  end.

Inductive References : Set :=
  ClassAttributesReference | AttributeTypeReference.

Definition getTypeByReference (type : References) : Set :=
  match type with
  | ClassAttributesReference => ClassAttributes
  | AttributeTypeReference => AttributeType
  end.

Definition getERoleTypesByReference (c: References): Set :=
  match c with
  | ClassAttributesReference => (Class * list Attribute)
  | AttributeTypeReference => (Attribute * Class)
  end.

(* Generic types *)

Inductive Object : Set :=
| BuildObject : forall (c:Classes), (getTypeByClass c) -> Object.

Definition beq_Object (c1 : Object) (c2 : Object) : bool :=
  match c1, c2 with
  | BuildObject ClassClass o1, BuildObject ClassClass o2 => beq_Class o1 o2
  | BuildObject AttributeClass o1, BuildObject AttributeClass o2 => beq_Attribute o1 o2
  | _, _ => false
  end.

Inductive Link : Set :=
| BuildLink : forall (c:References), (getTypeByReference c) -> Link.


(* Reflective functions *)

Lemma eqClass_dec : forall (c1:Classes) (c2:Classes), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Lemma eqReference_dec : forall (c1:References) (c2:References), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Definition getClass (c : Object) : Classes :=
   match c with
  | (BuildObject c _) => c
   end.

Definition getReference (c : Link) : References :=
   match c with
  | (BuildLink c _) => c
   end.

Definition instanceOfClass (cmc: Classes) (c : Object): bool :=
  if eqClass_dec (getClass c) cmc then true else false.

Definition instanceOfReference (cmr: References) (c : Link): bool :=
  if eqReference_dec (getReference c) cmr then true else false.

Definition getObjectFromEAttributeValues (t : Classes) : (getEAttributeTypesByClass t) -> Object :=
  match t with
  | ClassClass => (fun (p: nat * string) => (BuildObject ClassClass (Build_Class (fst p) (snd p))))
  | AttributeClass => (fun (p: nat * bool * string) => (BuildObject AttributeClass (Build_Attribute (fst (fst p)) (snd (fst p)) (snd p))))
  end.

Definition getLinkFromERoleValues (t : References) : (getERoleTypesByReference t) -> Link :=
  match t with
  | ClassAttributesReference => (fun (p: Class * list Attribute) => (BuildLink ClassAttributesReference (Build_ClassAttributes (fst p) (snd p))))
  | AttributeTypeReference => (fun (p: Attribute * Class) => (BuildLink AttributeTypeReference (Build_AttributeType (fst p) (snd p))))
  end.

Definition toClass (t : Classes) (c : Object) : option (getTypeByClass t).
Proof.
  destruct c.
  destruct (eqClass_dec c t).
  - rewrite e in g.
    exact (Some g).
  - exact None.
Defined.



(*  
match c with
| ClassMetamodel_BuildObject c0 d =>
    let s := ClassMetamodel_eqClass_dec c0 t in
    match s with
    | left e => match e with
                     eq_refl => Some d
               end
    | right _ => None
    end
  end.
  
*)

Definition toReference (t : References) (c : Link) : option (getTypeByReference t).
Proof.
  destruct c.
  destruct (eqReference_dec t c).
  - rewrite <- e in g.
    exact (Some g).
  - exact None.
Defined.

(* Generic functions *)

Definition toObjectFromClass (c :Class) : Object :=
  (BuildObject ClassClass c).

Definition toObjectFromAttribute (a :Attribute) : Object :=
  (BuildObject AttributeClass a).

Definition toObject (t: Classes) (e: getTypeByClass t) : Object :=
  (BuildObject t e).

Definition toLink (t: References) (e: getTypeByReference t) : Link :=
  (BuildLink t e).

Definition getId (c : Object) : nat :=
  match c with
  | (BuildObject ClassClass c) => class_id c
  | (BuildObject AttributeClass a) => attr_id a
  end.

Definition getName (c : Object) : string :=
  match c with
  | (BuildObject ClassClass c) => class_name c
  | (BuildObject AttributeClass a) => attr_name a
  end.

(*Definition allClasses (m : ClassModel) : list Class :=
  match m with BuildClassModel l _ => optionList2List (map (ClassMetamodel_toClass ClassClass) l) end.*)

(*Theorem allClassesInModel :
  forall (c : Class) (cm: ClassModel), (In c (allClasses cm)) -> (In (ClassMetamodel_BuildObject ClassClass c) (allClassModelElements cm)).
Proof.
  intros.
  destruct cm.
  unfold allClassModelElements.
  unfold allClasses in H.
  apply all_optionList2List_in_list in H.
  induction l.
  - inversion H.
  - simpl in H. simpl.
    destruct H.
    + unfold ClassMetamodel_toClass in H.
      left.
      destruct (ClassMetamodel_eqClass_dec (ClassMetamodel_getClass a) ClassClass).
      * destruct a.
        -- inversion H. reflexivity.
        -- inversion H.
      * inversion H.
    + right.
      apply IHl.
      apply H.
Qed.*)
  
(*Definition allAttributes (m : ClassModel) : list Attribute :=
  match m with BuildClassModel l _ => optionList2List (map (ClassMetamodel_toClass AttributeClass) l) end.*)

Fixpoint getClassAttributesOnLinks (c : Class) (l : list Link) : option (list Attribute) :=
  match l with
  | (BuildLink ClassAttributesReference (Build_ClassAttributes cl a)) :: l1 => if beq_Class cl c then Some a else getClassAttributesOnLinks c l1
  | _ :: l1 => getClassAttributesOnLinks c l1
  | nil => None
  end.

Definition getClassAttributes (c : Class) (m : Model Object Link) : option (list Attribute) :=
  getClassAttributesOnLinks c (@allModelLinks _ _ m).

Definition getClassAttributesObjects (c : Class) (m : Model Object Link) : option (list Object) :=
  match getClassAttributes c m with
  | Some l => Some (map toObjectFromAttribute l)
  | _ => None
  end.

Fixpoint getAttributeTypeOnLinks (a : Attribute) (l : list Link) : option Class :=
  match l with
  | (BuildLink AttributeTypeReference (Build_AttributeType att c)) :: l1 => if beq_Attribute att a then Some c else getAttributeTypeOnLinks a l1
  | _ :: l1 => getAttributeTypeOnLinks a l1
  | nil => None
  end.

Definition getAttributeType (a : Attribute) (m : Model Object Link) : option Class :=
  match m with
    (Build_Model cs ls) => getAttributeTypeOnLinks a ls
  end.

Definition getAttributeTypeObject (a : Attribute) (m : Model Object Link) : option Object :=
  match getAttributeType a m with
  | Some c => Some (toObject ClassClass c)
  | None => None
  end.

Definition defaultInstanceOfClass (c: Classes) : (getTypeByClass c) :=
  match c with
  | ClassClass => (Build_Class 0 "")
  | AttributeClass => (Build_Attribute 0 false "")
  end.

(* Typeclass Instance *)

#[export]
Instance ClassElementSum : Sum Object Classes :=
{
  denoteSubType := getTypeByClass;
  toSubType := toClass;
  toSumType := toObject;
}.

(* TODO *)
Definition beq_Link (c1 : Link) (c2 : Link) : bool := true.

#[export]
Instance ClassLinkSum : Sum Link References :=
{
  denoteSubType := getTypeByReference;
  toSubType := toReference;
  toSumType := toLink;
}.

#[export]
Instance EqDec : EqDec Object := {
    eq_b := beq_Object;
}.

#[export]
Instance ClassM : Metamodel :=
{
  ModelElement := Object;
  ModelLink := Link;
}.

#[export]
Instance ClassMetamodel : ModelingMetamodel ClassM :=
{ 
    elements := ClassElementSum;
    links := ClassLinkSum; 
}.

Definition ClassModel : Set := Model Object Link.

(* Useful lemmas *)
Lemma Class_invert : 
  forall (clec_arg: Classes) (t1 t2: getTypeByClass clec_arg), BuildObject clec_arg t1 = BuildObject clec_arg t2 -> t1 = t2.
Proof.
  intros.
  inversion H.
  apply inj_pair2_eq_dec in H1.
  exact H1.
  apply eqClass_dec.
Qed.

Lemma Object_dec: 
  forall (a: Object),
    (instanceOfClass ClassClass a) = true
 \/ (instanceOfClass AttributeClass a) = true.
Proof.
  intros.
  destruct a.
  destruct c.
  + left. crush.
  + right. crush.
Qed.

Lemma Class_Object_cast:
  forall a c,
    toClass ClassClass a = return c ->
      toObject ClassClass c = a.
Proof.
  intros.
  unfold toClass in H.
  destruct a.
  unfold instanceOfClass in H.
  simpl in H.
  destruct (eqClass_dec c0 ClassClass); crush.
Qed.

Lemma Attribute_Object_cast:
  forall a c,
    toClass AttributeClass a = return c ->
      toObject AttributeClass c = a.
Proof.
  intros.
  unfold toClass in H.
  destruct a.
  unfold instanceOfClass in H.
  simpl in H.
  destruct (eqClass_dec c0 AttributeClass); crush.
Qed.

Lemma Class_dec :
  forall x y : Class, {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply String.string_dec.
  - apply Nat.eq_dec.
Qed.

Lemma Attribute_dec :
  forall x y : Attribute, {x = y} + {x <> y}.
Proof.
  decide equality.
  - apply String.string_dec.
  - apply Bool.bool_dec.
  - apply Nat.eq_dec.
Qed.

Lemma eq_dec : forall (x y : Object), {x = y} + {x <> y}.
  intros.
  destruct x as [[] x], y as [[] y]; try (right; discriminate).
  - destruct (Class_dec x y) as [H | H].
    + left. congruence.
    + right. contradict H.
      inversion H.
      apply Eqdep.EqdepTheory.inj_pair2 in H1.
      assumption.
  - destruct (Attribute_dec x y) as [H | H].
    + left. congruence.
    + right. contradict H.
      inversion H.
      apply Eqdep.EqdepTheory.inj_pair2 in H1.
      assumption.
Qed.
