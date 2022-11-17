

(********************************************************************
	@name Coq declarations for metamodel: <Families>
	@date 2021/11/22 10:07:56
	@description Automatically generated by Ecore2Coq transformation.
 ********************************************************************)

(* Coq libraries *)
Require Import String.
Require Import Bool.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import PeanoNat.
Require Import EqNat.
Require Import Coq.Logic.Eqdep_dec.
Scheme Equality for option. (* equality for option type *)

Require Import core.EqDec.
Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.utils.CpdtTactics.

(* Base types *)


Inductive Family : Set :=
  BuildFamily :
  (* lastName *)  string ->
  Family.

Inductive Member : Set :=
  BuildMember :
  (* firstName *)  string ->
  Member.


Inductive FamilyFfather : Set :=
   BuildFamilyFfather :
   Family ->
   Member ->
   FamilyFfather.

Definition maybeBuildFamilyFfather (fa_arg: Family) (ff_arg: option (Member)) : option FamilyFfather :=
  match fa_arg, ff_arg with
  | fa_arg_succ, Some ff_arg_succ => Some (BuildFamilyFfather fa_arg_succ ff_arg_succ)
  | _, _ => None
  end.
Inductive FamilyFmother : Set :=
   BuildFamilyFmother :
   Family ->
   Member ->
   FamilyFmother.

Definition maybeBuildFamilyFmother (fa_arg: Family) (fm_arg: option (Member)) : option FamilyFmother :=
  match fa_arg, fm_arg with
  | fa_arg_succ, Some fm_arg_succ => Some (BuildFamilyFmother fa_arg_succ fm_arg_succ)
  | _, _ => None
  end.
Inductive FamilyFsons : Set :=
   BuildFamilyFsons :
   Family ->
   list Member ->
   FamilyFsons.

Definition maybeBuildFamilyFsons (fa_arg: Family) (fs_arg: option (list Member)) : option FamilyFsons :=
  match fa_arg, fs_arg with
  | fa_arg_succ, Some fs_arg_succ => Some (BuildFamilyFsons fa_arg_succ fs_arg_succ)
  | _, _ => None
  end.
Inductive FamilyFdaughters : Set :=
   BuildFamilyFdaughters :
   Family ->
   list Member ->
   FamilyFdaughters.

Definition maybeBuildFamilyFdaughters (fa_arg: Family) (fd_arg: option (list Member)) : option FamilyFdaughters :=
  match fa_arg, fd_arg with
  | fa_arg_succ, Some fd_arg_succ => Some (BuildFamilyFdaughters fa_arg_succ fd_arg_succ)
  | _, _ => None
  end.

Inductive MemberFamilyFather : Set :=
   BuildMemberFamilyFather :
   Member ->
   Family ->
   MemberFamilyFather.

Definition maybeBuildMemberFamilyFather (me_arg: Member) (fa_arg: option (Family)) : option MemberFamilyFather :=
  match me_arg, fa_arg with
  | me_arg_succ, Some fa_arg_succ => Some (BuildMemberFamilyFather me_arg_succ fa_arg_succ)
  | _, _ => None
  end.
Inductive MemberFamilyMother : Set :=
   BuildMemberFamilyMother :
   Member ->
   Family ->
   MemberFamilyMother.

Definition maybeBuildMemberFamilyMother (me_arg: Member) (fa_arg: option (Family)) : option MemberFamilyMother :=
  match me_arg, fa_arg with
  | me_arg_succ, Some fa_arg_succ => Some (BuildMemberFamilyMother me_arg_succ fa_arg_succ)
  | _, _ => None
  end.
Inductive MemberFamilySon : Set :=
   BuildMemberFamilySon :
   Member ->
   Family ->
   MemberFamilySon.

Definition maybeBuildMemberFamilySon (me_arg: Member) (fa_arg: option (Family)) : option MemberFamilySon :=
  match me_arg, fa_arg with
  | me_arg_succ, Some fa_arg_succ => Some (BuildMemberFamilySon me_arg_succ fa_arg_succ)
  | _, _ => None
  end.
Inductive MemberFamilyDaughter : Set :=
   BuildMemberFamilyDaughter :
   Member ->
   Family ->
   MemberFamilyDaughter.

Definition maybeBuildMemberFamilyDaughter (me_arg: Member) (fa_arg: option (Family)) : option MemberFamilyDaughter :=
  match me_arg, fa_arg with
  | me_arg_succ, Some fa_arg_succ => Some (BuildMemberFamilyDaughter me_arg_succ fa_arg_succ)
  | _, _ => None
  end.



(* Accessors *)
Definition Family_getLastName (f : Family) :  string :=
  match f with BuildFamily  lastName  => lastName end.

Definition Member_getFirstName (m : Member) :  string :=
  match m with BuildMember  firstName  => firstName end.


Definition beq_Family (fa_arg1 : Family) (fa_arg2 : Family) : bool :=
(  beq_string (Family_getLastName fa_arg1) (Family_getLastName fa_arg2) )
.

Definition beq_Member (me_arg1 : Member) (me_arg2 : Member) : bool :=
(  beq_string (Member_getFirstName me_arg1) (Member_getFirstName me_arg2) )
.


(* Meta-types *)	
Inductive FamiliesMetamodel_Class : Set :=
  | FamilyClass
  | MemberClass
.

Definition FamiliesMetamodel_getTypeByClass (facl_arg : FamiliesMetamodel_Class) : Set :=
  match facl_arg with
    | FamilyClass => Family
    | MemberClass => Member
  end.	

Inductive FamiliesMetamodel_Reference : Set :=
| FamilyFfatherReference
| FamilyFmotherReference
| FamilyFsonsReference
| FamilyFdaughtersReference
| MemberFamilyFatherReference
| MemberFamilyMotherReference
| MemberFamilySonReference
| MemberFamilyDaughterReference
.

Definition FamiliesMetamodel_getTypeByReference (fare_arg : FamiliesMetamodel_Reference) : Set :=
  match fare_arg with
| FamilyFfatherReference => FamilyFfather
| FamilyFmotherReference => FamilyFmother
| FamilyFsonsReference => FamilyFsons
| FamilyFdaughtersReference => FamilyFdaughters
| MemberFamilyFatherReference => MemberFamilyFather
| MemberFamilyMotherReference => MemberFamilyMother
| MemberFamilySonReference => MemberFamilySon
| MemberFamilyDaughterReference => MemberFamilyDaughter
  end.

Definition FamiliesMetamodel_getERoleTypesByEReference (fare_arg : FamiliesMetamodel_Reference) : Set :=
  match fare_arg with
| FamilyFfatherReference => (Family * Member)
| FamilyFmotherReference => (Family * Member)
| FamilyFsonsReference => (Family * list Member)
| FamilyFdaughtersReference => (Family * list Member)
| MemberFamilyFatherReference => (Member * Family)
| MemberFamilyMotherReference => (Member * Family)
| MemberFamilySonReference => (Member * Family)
| MemberFamilyDaughterReference => (Member * Family)
  end.

(* Generic types *)			
Inductive FamiliesMetamodel_Object : Set :=
 | Build_FamiliesMetamodel_Object : 
    forall (facl_arg: FamiliesMetamodel_Class), (FamiliesMetamodel_getTypeByClass facl_arg) -> FamiliesMetamodel_Object.

Definition beq_FamiliesMetamodel_Object (c1 : FamiliesMetamodel_Object) (c2 : FamiliesMetamodel_Object) : bool :=
  match c1, c2 with
  | Build_FamiliesMetamodel_Object FamilyClass o1, Build_FamiliesMetamodel_Object FamilyClass o2 => beq_Family o1 o2
  | Build_FamiliesMetamodel_Object MemberClass o1, Build_FamiliesMetamodel_Object MemberClass o2 => beq_Member o1 o2
  | _, _ => false
  end.

Inductive FamiliesMetamodel_Link : Set :=
 | Build_FamiliesMetamodel_Link : 
    forall (fare_arg:FamiliesMetamodel_Reference), (FamiliesMetamodel_getTypeByReference fare_arg) -> FamiliesMetamodel_Link.

(* TODO *)
Definition beq_FamiliesMetamodel_Link (l1 : FamiliesMetamodel_Link) (l2 : FamiliesMetamodel_Link) : bool := true.

(* Reflective functions *)
Lemma FamiliesMetamodel_eqEClass_dec : 
 forall (facl_arg1:FamiliesMetamodel_Class) (facl_arg2:FamiliesMetamodel_Class), { facl_arg1 = facl_arg2 } + { facl_arg1 <> facl_arg2 }.
Proof. repeat decide equality. Defined.

Lemma FamiliesMetamodel_eqEReference_dec : 
 forall (fare_arg1:FamiliesMetamodel_Reference) (fare_arg2:FamiliesMetamodel_Reference), { fare_arg1 = fare_arg2 } + { fare_arg1 <> fare_arg2 }.
Proof. repeat decide equality. Defined.

Definition FamiliesMetamodel_getEClass (faob_arg : FamiliesMetamodel_Object) : FamiliesMetamodel_Class :=
   match faob_arg with
  | (Build_FamiliesMetamodel_Object faob_arg _) => faob_arg
   end.

Definition FamiliesMetamodel_getEReference (fali_arg : FamiliesMetamodel_Link) : FamiliesMetamodel_Reference :=
   match fali_arg with
  | (Build_FamiliesMetamodel_Link fali_arg _) => fali_arg
   end.

Definition FamiliesMetamodel_instanceOfEClass (facl_arg: FamiliesMetamodel_Class) (faob_arg : FamiliesMetamodel_Object): bool :=
  if FamiliesMetamodel_eqEClass_dec (FamiliesMetamodel_getEClass faob_arg) facl_arg then true else false.

Definition FamiliesMetamodel_instanceOfEReference (fare_arg: FamiliesMetamodel_Reference) (fali_arg : FamiliesMetamodel_Link): bool :=
  if FamiliesMetamodel_eqEReference_dec (FamiliesMetamodel_getEReference fali_arg) fare_arg then true else false.


Definition FamiliesMetamodel_toClass (facl_arg : FamiliesMetamodel_Class) (faob_arg : FamiliesMetamodel_Object) : option (FamiliesMetamodel_getTypeByClass facl_arg).
Proof.
  destruct faob_arg as [arg1 arg2].
  destruct (FamiliesMetamodel_eqEClass_dec arg1 facl_arg) as [e|] eqn:dec_case.
  - rewrite e in arg2.
    exact (Some arg2).
  - exact None.
Defined.

Definition FamiliesMetamodel_toReference (fare_arg : FamiliesMetamodel_Reference) (fali_arg : FamiliesMetamodel_Link) : option (FamiliesMetamodel_getTypeByReference fare_arg).
Proof.
  destruct fali_arg as [arg1 arg2].
  destruct (FamiliesMetamodel_eqEReference_dec arg1 fare_arg) as [e|] eqn:dec_case.
  - rewrite e in arg2.
  	exact (Some arg2).
  - exact None.
Defined.

(* Generic functions *)
Definition FamiliesModel := Model FamiliesMetamodel_Object FamiliesMetamodel_Link.

Definition FamiliesMetamodel_toObject (facl_arg: FamiliesMetamodel_Class) (t: FamiliesMetamodel_getTypeByClass facl_arg) : FamiliesMetamodel_Object :=
  (Build_FamiliesMetamodel_Object facl_arg t).

Definition FamiliesMetamodel_toLink (fare_arg: FamiliesMetamodel_Reference) (t: FamiliesMetamodel_getTypeByReference fare_arg) : FamiliesMetamodel_Link :=
  (Build_FamiliesMetamodel_Link fare_arg t).




Fixpoint Family_getFfatherOnLinks (fa_arg : Family) (l : list FamiliesMetamodel_Link) : option (Member) :=
match l with
| (Build_FamiliesMetamodel_Link FamilyFfatherReference (BuildFamilyFfather Family_ctr ffather_ctr)) :: l' => 
	  if beq_Family Family_ctr fa_arg then Some ffather_ctr else Family_getFfatherOnLinks fa_arg l'
| _ :: l' => Family_getFfatherOnLinks fa_arg l'
| nil => None
end.

Definition Family_getFfather (fa_arg : Family) (m : FamiliesModel) : option (Member) :=
  Family_getFfatherOnLinks fa_arg (@allModelLinks _ _ m).
  
Definition Family_getFfatherObject (fa_arg : Family) (m : FamiliesModel) : option (FamiliesMetamodel_Object) :=
  match Family_getFfather fa_arg m with
  | Some me_arg => Some (FamiliesMetamodel_toObject MemberClass me_arg) 
  | _ => None
  end.
Fixpoint Family_getFmotherOnLinks (fa_arg : Family) (l : list FamiliesMetamodel_Link) : option (Member) :=
match l with
| (Build_FamiliesMetamodel_Link FamilyFmotherReference (BuildFamilyFmother Family_ctr fmother_ctr)) :: l' => 
	  if beq_Family Family_ctr fa_arg then Some fmother_ctr else Family_getFmotherOnLinks fa_arg l'
| _ :: l' => Family_getFmotherOnLinks fa_arg l'
| nil => None
end.

Definition Family_getFmother (fa_arg : Family) (m : FamiliesModel) : option (Member) :=
  Family_getFmotherOnLinks fa_arg (@allModelLinks _ _ m).
  
Definition Family_getFmotherObject (fa_arg : Family) (m : FamiliesModel) : option (FamiliesMetamodel_Object) :=
  match Family_getFmother fa_arg m with
  | Some me_arg => Some (FamiliesMetamodel_toObject MemberClass me_arg) 
  | _ => None
  end.
Fixpoint Family_getFsonsOnLinks (fa_arg : Family) (l : list FamiliesMetamodel_Link) : option (list Member) :=
match l with
| (Build_FamiliesMetamodel_Link FamilyFsonsReference (BuildFamilyFsons Family_ctr fsons_ctr)) :: l' => 
	  if beq_Family Family_ctr fa_arg then Some fsons_ctr else Family_getFsonsOnLinks fa_arg l'
| _ :: l' => Family_getFsonsOnLinks fa_arg l'
| nil => None
end.

Definition Family_getFsons (fa_arg : Family) (m : FamiliesModel) : option (list Member) :=
  Family_getFsonsOnLinks fa_arg (@allModelLinks _ _ m).
  
Definition Family_getFsonsObjects (fa_arg : Family) (m : FamiliesModel) : option (list FamiliesMetamodel_Object) :=
  match Family_getFsons fa_arg m with
  | Some l => Some (map (FamiliesMetamodel_toObject MemberClass) l)
  | _ => None
  end.
Fixpoint Family_getFdaughtersOnLinks (fa_arg : Family) (l : list FamiliesMetamodel_Link) : option (list Member) :=
match l with
| (Build_FamiliesMetamodel_Link FamilyFdaughtersReference (BuildFamilyFdaughters Family_ctr fdaughters_ctr)) :: l' => 
	  if beq_Family Family_ctr fa_arg then Some fdaughters_ctr else Family_getFdaughtersOnLinks fa_arg l'
| _ :: l' => Family_getFdaughtersOnLinks fa_arg l'
| nil => None
end.

Definition Family_getFdaughters (fa_arg : Family) (m : FamiliesModel) : option (list Member) :=
  Family_getFdaughtersOnLinks fa_arg (@allModelLinks _ _ m).
  
Definition Family_getFdaughtersObjects (fa_arg : Family) (m : FamiliesModel) : option (list FamiliesMetamodel_Object) :=
  match Family_getFdaughters fa_arg m with
  | Some l => Some (map (FamiliesMetamodel_toObject MemberClass) l)
  | _ => None
  end.

Fixpoint Member_getFamilyFatherOnLinks (me_arg : Member) (l : list FamiliesMetamodel_Link) : option (Family) :=
match l with
| (Build_FamiliesMetamodel_Link MemberFamilyFatherReference (BuildMemberFamilyFather Member_ctr familyFather_ctr)) :: l' => 
	  if beq_Member Member_ctr me_arg then Some familyFather_ctr else Member_getFamilyFatherOnLinks me_arg l'
| _ :: l' => Member_getFamilyFatherOnLinks me_arg l'
| nil => None
end.

Definition Member_getFamilyFather (me_arg : Member) (m : FamiliesModel) : option (Family) :=
  Member_getFamilyFatherOnLinks me_arg (@allModelLinks _ _ m).
  
Definition Member_getFamilyFatherObject (me_arg : Member) (m : FamiliesModel) : option (FamiliesMetamodel_Object) :=
  match Member_getFamilyFather me_arg m with
  | Some fa_arg => Some (FamiliesMetamodel_toObject FamilyClass fa_arg) 
  | _ => None
  end.
Fixpoint Member_getFamilyMotherOnLinks (me_arg : Member) (l : list FamiliesMetamodel_Link) : option (Family) :=
match l with
| (Build_FamiliesMetamodel_Link MemberFamilyMotherReference (BuildMemberFamilyMother Member_ctr familyMother_ctr)) :: l' => 
	  if beq_Member Member_ctr me_arg then Some familyMother_ctr else Member_getFamilyMotherOnLinks me_arg l'
| _ :: l' => Member_getFamilyMotherOnLinks me_arg l'
| nil => None
end.

Definition Member_getFamilyMother (me_arg : Member) (m : FamiliesModel) : option (Family) :=
  Member_getFamilyMotherOnLinks me_arg (@allModelLinks _ _ m).
  
Definition Member_getFamilyMotherObject (me_arg : Member) (m : FamiliesModel) : option (FamiliesMetamodel_Object) :=
  match Member_getFamilyMother me_arg m with
  | Some fa_arg => Some (FamiliesMetamodel_toObject FamilyClass fa_arg) 
  | _ => None
  end.
Fixpoint Member_getFamilySonOnLinks (me_arg : Member) (l : list FamiliesMetamodel_Link) : option (Family) :=
match l with
| (Build_FamiliesMetamodel_Link MemberFamilySonReference (BuildMemberFamilySon Member_ctr familySon_ctr)) :: l' => 
	  if beq_Member Member_ctr me_arg then Some familySon_ctr else Member_getFamilySonOnLinks me_arg l'
| _ :: l' => Member_getFamilySonOnLinks me_arg l'
| nil => None
end.

Definition Member_getFamilySon (me_arg : Member) (m : FamiliesModel) : option (Family) :=
  Member_getFamilySonOnLinks me_arg (@allModelLinks _ _ m).
  
Definition Member_getFamilySonObject (me_arg : Member) (m : FamiliesModel) : option (FamiliesMetamodel_Object) :=
  match Member_getFamilySon me_arg m with
  | Some fa_arg => Some (FamiliesMetamodel_toObject FamilyClass fa_arg) 
  | _ => None
  end.
Fixpoint Member_getFamilyDaughterOnLinks (me_arg : Member) (l : list FamiliesMetamodel_Link) : option (Family) :=
match l with
| (Build_FamiliesMetamodel_Link MemberFamilyDaughterReference (BuildMemberFamilyDaughter Member_ctr familyDaughter_ctr)) :: l' => 
	  if beq_Member Member_ctr me_arg then Some familyDaughter_ctr else Member_getFamilyDaughterOnLinks me_arg l'
| _ :: l' => Member_getFamilyDaughterOnLinks me_arg l'
| nil => None
end.

Definition Member_getFamilyDaughter (me_arg : Member) (m : FamiliesModel) : option (Family) :=
  Member_getFamilyDaughterOnLinks me_arg (@allModelLinks _ _ m).
  
Definition Member_getFamilyDaughterObject (me_arg : Member) (m : FamiliesModel) : option (FamiliesMetamodel_Object) :=
  match Member_getFamilyDaughter me_arg m with
  | Some fa_arg => Some (FamiliesMetamodel_toObject FamilyClass fa_arg) 
  | _ => None
  end.


(* Typeclass Instances *)	

#[export]
Instance FamiliesMetamodel_ElementSum : Sum FamiliesMetamodel_Object FamiliesMetamodel_Class :=
{
	denoteSubType := FamiliesMetamodel_getTypeByClass;
	toSubType := FamiliesMetamodel_toClass;
	toSumType := FamiliesMetamodel_toObject;
}.

#[export]
Instance FamiliesMetamodel_LinkSum : Sum FamiliesMetamodel_Link FamiliesMetamodel_Reference :=
{
	denoteSubType := FamiliesMetamodel_getTypeByReference;
	toSubType := FamiliesMetamodel_toReference;
	toSumType := FamiliesMetamodel_toLink;
}.


#[export]
Instance FamiliesMetamodel_Metamodel_Instance : 
	Metamodel :=
{
	ModelElement := FamiliesMetamodel_Object;
	ModelLink := FamiliesMetamodel_Link;
        elements_eqdec := beq_FamiliesMetamodel_Object
}.

#[export]
Instance FamiliesMetamodel_ModelingMetamodel_Instance : 
	ModelingMetamodel FamiliesMetamodel_Metamodel_Instance :=
{ 
    elements := FamiliesMetamodel_ElementSum;
    links := FamiliesMetamodel_LinkSum; 
}.

(* Useful lemmas *)

Lemma Families_invert : 
  forall (facl_arg: FamiliesMetamodel_Class) (t1 t2: FamiliesMetamodel_getTypeByClass facl_arg), 
    Build_FamiliesMetamodel_Object facl_arg t1 = Build_FamiliesMetamodel_Object facl_arg t2 -> t1 = t2.
Admitted.
