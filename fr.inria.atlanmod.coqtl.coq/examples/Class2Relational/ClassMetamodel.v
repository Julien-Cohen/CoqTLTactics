Require Import String.
Require Import Bool.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Omega.
Require Import Coq.Logic.Eqdep_dec.


Require Import core.utils.TopUtils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.utils.CpdtTactics.
(* Base types *)

Inductive Class : Set :=
    BuildClass :
      (* id *) nat ->
      (* name *) string -> Class.

Inductive Attribute : Set :=
    BuildAttribute :
      (* id *) nat ->
      (* derived *) bool ->
      (* name *) string -> Attribute.

Inductive ClassAttributes : Set :=
    BuildClassAttributes:
      Class ->
      list Attribute -> ClassAttributes.

Inductive AttributeType : Set :=
    BuildAttributeType:
      Attribute ->
      Class -> AttributeType.

(* Accessors *)

Definition getClassId (c : Class) : nat :=
  match c with BuildClass id _ => id end.

Definition getClassName (c : Class) : string :=
  match c with BuildClass _ n => n end.

Definition getAttributeId (a : Attribute) : nat :=
  match a with BuildAttribute id _ _ => id end.

Definition getAttributeName (a : Attribute) : string :=
  match a with BuildAttribute _ _ n => n end.

Definition getAttributeDerived (a : Attribute) : bool :=
  match a with BuildAttribute _ n _ => n end.

Definition beq_Class (c1 : Class) (c2 : Class) : bool :=
  beq_nat (getClassId c1) (getClassId c2) && beq_string (getClassName c1) (getClassName c2).

Definition beq_Attribute (a1 : Attribute) (a2 : Attribute) : bool :=
  beq_nat (getAttributeId a1) (getAttributeId a2) && eqb (getAttributeDerived a1) (getAttributeDerived a2) && beq_string (getAttributeName a1) (getAttributeName a2).

Lemma lem_beq_Class_id:
 forall (a1 a2: Class),
   beq_Class a1 a2 = true -> a1 = a2.
Proof.
intros.
unfold beq_Class in H.
unfold "&&" in H.
destruct (getClassId a1 =? getClassId a2) eqn: ca1.
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
destruct (getAttributeId a1 =? getAttributeId a2) eqn: ca1.
- destruct (eqb (getAttributeDerived a1) (getAttributeDerived a2)) eqn: ca2.
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

Inductive ClassMetamodel_Class : Set :=
  ClassClass | AttributeClass.

Definition ClassMetamodel_getTypeByClass (type : ClassMetamodel_Class) : Set :=
  match type with
  | ClassClass => Class
  | AttributeClass => Attribute
  end.

Definition ClassMetamodel_getEAttributeTypesByClass (c: ClassMetamodel_Class): Set :=
  match c with
  | ClassClass => (nat * string)
  | AttributeClass => (nat * bool * string)
  end.

Inductive ClassMetamodel_EReference : Set :=
  ClassAttributesEReference | AttributeTypeEReference.

Definition ClassMetamodel_getTypeByEReference (type : ClassMetamodel_EReference) : Set :=
  match type with
  | ClassAttributesEReference => ClassAttributes
  | AttributeTypeEReference => AttributeType
  end.

Definition ClassMetamodel_getERoleTypesByEReference (c: ClassMetamodel_EReference): Set :=
  match c with
  | ClassAttributesEReference => (Class * list Attribute)
  | AttributeTypeEReference => (Attribute * Class)
  end.

(* Generic types *)

Inductive ClassMetamodel_Object : Set :=
| ClassMetamodel_BuildObject : forall (c:ClassMetamodel_Class), (ClassMetamodel_getTypeByClass c) -> ClassMetamodel_Object.

Definition beq_ClassMetamodel_Object (c1 : ClassMetamodel_Object) (c2 : ClassMetamodel_Object) : bool :=
  match c1, c2 with
  | ClassMetamodel_BuildObject ClassClass o1, ClassMetamodel_BuildObject ClassClass o2 => beq_Class o1 o2
  | ClassMetamodel_BuildObject AttributeClass o1, ClassMetamodel_BuildObject AttributeClass o2 => beq_Attribute o1 o2
  | _, _ => false
  end.

Inductive ClassMetamodel_ELink : Set :=
| ClassMetamodel_BuildELink : forall (c:ClassMetamodel_EReference), (ClassMetamodel_getTypeByEReference c) -> ClassMetamodel_ELink.


(* Reflective functions *)

Lemma ClassMetamodel_eqClass_dec : forall (c1:ClassMetamodel_Class) (c2:ClassMetamodel_Class), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Lemma ClassMetamodel_eqEReference_dec : forall (c1:ClassMetamodel_EReference) (c2:ClassMetamodel_EReference), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Definition ClassMetamodel_getClass (c : ClassMetamodel_Object) : ClassMetamodel_Class :=
   match c with
  | (ClassMetamodel_BuildObject c _) => c
   end.

Definition ClassMetamodel_getEReference (c : ClassMetamodel_ELink) : ClassMetamodel_EReference :=
   match c with
  | (ClassMetamodel_BuildELink c _) => c
   end.

Definition ClassMetamodel_instanceOfClass (cmc: ClassMetamodel_Class) (c : ClassMetamodel_Object): bool :=
  if ClassMetamodel_eqClass_dec (ClassMetamodel_getClass c) cmc then true else false.

Definition ClassMetamodel_instanceOfEReference (cmr: ClassMetamodel_EReference) (c : ClassMetamodel_ELink): bool :=
  if ClassMetamodel_eqEReference_dec (ClassMetamodel_getEReference c) cmr then true else false.

Definition ClassMetamodel_getObjectFromEAttributeValues (t : ClassMetamodel_Class) : (ClassMetamodel_getEAttributeTypesByClass t) -> ClassMetamodel_Object :=
  match t with
  | ClassClass => (fun (p: nat * string) => (ClassMetamodel_BuildObject ClassClass (BuildClass (fst p) (snd p))))
  | AttributeClass => (fun (p: nat * bool * string) => (ClassMetamodel_BuildObject AttributeClass (BuildAttribute (fst (fst p)) (snd (fst p)) (snd p))))
  end.

Definition ClassMetamodel_getELinkFromERoleValues (t : ClassMetamodel_EReference) : (ClassMetamodel_getERoleTypesByEReference t) -> ClassMetamodel_ELink :=
  match t with
  | ClassAttributesEReference => (fun (p: Class * list Attribute) => (ClassMetamodel_BuildELink ClassAttributesEReference (BuildClassAttributes (fst p) (snd p))))
  | AttributeTypeEReference => (fun (p: Attribute * Class) => (ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType (fst p) (snd p))))
  end.

Definition ClassMetamodel_toClass (t : ClassMetamodel_Class) (c : ClassMetamodel_Object) : option (ClassMetamodel_getTypeByClass t).
Proof.
  destruct c.
  destruct (ClassMetamodel_eqClass_dec c t).
  - rewrite e in c0.
    exact (Some c0).
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

Definition ClassMetamodel_toEReference (t : ClassMetamodel_EReference) (c : ClassMetamodel_ELink) : option (ClassMetamodel_getTypeByEReference t).
Proof.
  destruct c.
  destruct (ClassMetamodel_eqEReference_dec t c).
  - rewrite <- e in c0.
    exact (Some c0).
  - exact None.
Defined.

(* Generic functions *)

Definition ClassMetamodel_toObjectFromClass (c :Class) : ClassMetamodel_Object :=
  (ClassMetamodel_BuildObject ClassClass c).
Coercion ClassMetamodel_toObjectFromClass : Class >-> ClassMetamodel_Object.
Definition ClassMetamodel_toObject (c : ClassMetamodel_Object) : ClassMetamodel_Object := c.

Definition ClassMetamodel_toObjectFromAttribute (a :Attribute) : ClassMetamodel_Object :=
  (ClassMetamodel_BuildObject AttributeClass a).
Coercion ClassMetamodel_toObjectFromAttribute : Attribute >-> ClassMetamodel_Object.
Definition ClassMetamodel_toELink (c : ClassMetamodel_ELink) : ClassMetamodel_ELink := c.

Definition ClassMetamodel_toObjectOfClass (t: ClassMetamodel_Class) (e: ClassMetamodel_getTypeByClass t) : ClassMetamodel_Object :=
  (ClassMetamodel_BuildObject t e).

Definition ClassMetamodel_toELinkOfEReference (t: ClassMetamodel_EReference) (e: ClassMetamodel_getTypeByEReference t) : ClassMetamodel_ELink :=
  (ClassMetamodel_BuildELink t e).

Definition ClassMetamodel_getId (c : ClassMetamodel_Object) : nat :=
  match c with
  | (ClassMetamodel_BuildObject ClassClass c) => getClassId c
  | (ClassMetamodel_BuildObject AttributeClass a) => getAttributeId a
  end.

Definition ClassMetamodel_getName (c : ClassMetamodel_Object) : string :=
  match c with
  | (ClassMetamodel_BuildObject ClassClass c) => getClassName c
  | (ClassMetamodel_BuildObject AttributeClass a) => getAttributeName a
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

Fixpoint ClassMetamodel_getClassAttributesOnLinks (c : Class) (l : list ClassMetamodel_ELink) : option (list Attribute) :=
  match l with
  | (ClassMetamodel_BuildELink ClassAttributesEReference (BuildClassAttributes cl a)) :: l1 => if beq_Class cl c then Some a else ClassMetamodel_getClassAttributesOnLinks c l1
  | _ :: l1 => ClassMetamodel_getClassAttributesOnLinks c l1
  | nil => None
  end.

Definition getClassAttributes (c : Class) (m : Model ClassMetamodel_Object ClassMetamodel_ELink) : option (list Attribute) :=
  ClassMetamodel_getClassAttributesOnLinks c (@allModelLinks _ _ m).

Fixpoint ClassMetamodel_getAttributeTypeOnLinks (a : Attribute) (l : list ClassMetamodel_ELink) : option Class :=
  match l with
  | (ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType att c)) :: l1 => if beq_Attribute att a then Some c else ClassMetamodel_getAttributeTypeOnLinks a l1
  | _ :: l1 => ClassMetamodel_getAttributeTypeOnLinks a l1
  | nil => None
  end.

Definition getAttributeType (a : Attribute) (m : Model ClassMetamodel_Object ClassMetamodel_ELink) : option Class :=
  match m with
    (Build_Model cs ls) => ClassMetamodel_getAttributeTypeOnLinks a ls
  end.

Definition ClassMetamodel_defaultInstanceOfClass (c: ClassMetamodel_Class) : (ClassMetamodel_getTypeByClass c) :=
  match c with
  | ClassClass => (BuildClass 0 "")
  | AttributeClass => (BuildAttribute 0 false "")
  end.

(* Typeclass Instance *)

Instance ClassMetamodel : Metamodel ClassMetamodel_Object ClassMetamodel_ELink ClassMetamodel_Class ClassMetamodel_EReference :=
  {
    denoteModelClass := ClassMetamodel_getTypeByClass;
    denoteModelReference := ClassMetamodel_getTypeByEReference;
    toModelClass := ClassMetamodel_toClass;
    toModelReference := ClassMetamodel_toEReference;
    toModelElement := ClassMetamodel_toObjectOfClass;
    toModelLink := ClassMetamodel_toELinkOfEReference;
    beq_ModelElement := beq_ClassMetamodel_Object;

    (* Theorems *)
    eqModelClass_dec := ClassMetamodel_eqClass_dec;
    eqModelReference_dec := ClassMetamodel_eqEReference_dec;
  }.

Definition ClassModel := Model ClassMetamodel_Object ClassMetamodel_ELink.

(* Useful lemmas *)
Lemma Class_invert : 
  forall (clec_arg: ClassMetamodel_Class) (t1 t2: ClassMetamodel_getTypeByClass clec_arg), ClassMetamodel_BuildObject clec_arg t1 = ClassMetamodel_BuildObject clec_arg t2 -> t1 = t2.
Proof.
  intros.
  inversion H.
  apply inj_pair2_eq_dec in H1.
  exact H1.
  apply ClassMetamodel_eqClass_dec.
Qed.

Lemma Object_dec: 
  forall (a: ClassMetamodel_Object),
    (ClassMetamodel_instanceOfClass ClassClass a) = true
 \/ (ClassMetamodel_instanceOfClass AttributeClass a) = true.
Proof.
  intros.
  destruct a.
  destruct c.
  + left. crush.
  + right. crush.
Qed.

Lemma Class_Object_cast:
  forall a c,
    ClassMetamodel_toClass ClassClass a = return c ->
      ClassMetamodel_toObject c = a.
Proof.
  intros.
  unfold ClassMetamodel_toClass in H.
  destruct a.
  unfold ClassMetamodel_instanceOfClass in H.
  simpl in H.
  destruct (ClassMetamodel_eqClass_dec c0 ClassClass); crush.
Qed.

Lemma Attribute_Object_cast:
  forall a c,
    ClassMetamodel_toClass AttributeClass a = return c ->
      ClassMetamodel_toObject c = a.
Proof.
  intros.
  unfold ClassMetamodel_toClass in H.
  destruct a.
  unfold ClassMetamodel_instanceOfClass in H.
  simpl in H.
  destruct (ClassMetamodel_eqClass_dec c0 AttributeClass); crush.
Qed.

