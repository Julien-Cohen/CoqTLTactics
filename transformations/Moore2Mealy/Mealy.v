

(********************************************************************
	@name Coq declarations for metamodel: <Mealy>
	@date 2022/01/29 12:14:52
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


Inductive State : Set :=
  BuildState :
  (* name *)  string ->
  State.

Inductive Transition : Set :=
  BuildTransition :
  (* input *)  string ->
  (* output *)  string ->
  Transition.



Inductive TransitionSource : Set :=
   BuildTransitionSource :
   Transition ->
   State ->
   TransitionSource.

Definition maybeBuildTransitionSource (tr_arg: Transition) (so_arg: option (State)) : option TransitionSource :=
  match tr_arg, so_arg with
  | tr_arg_succ, Some so_arg_succ => Some (BuildTransitionSource tr_arg_succ so_arg_succ)
  | _, _ => None
  end.
Inductive TransitionTarget : Set :=
   BuildTransitionTarget :
   Transition ->
   State ->
   TransitionTarget.

Definition maybeBuildTransitionTarget (tr_arg: Transition) (ta_arg: option (State)) : option TransitionTarget :=
  match tr_arg, ta_arg with
  | tr_arg_succ, Some ta_arg_succ => Some (BuildTransitionTarget tr_arg_succ ta_arg_succ)
  | _, _ => None
  end.



(* Accessors *)
Definition State_getName (s : State) :  string :=
  match s with BuildState  name  => name end.

Definition Transition_getInput (t : Transition) :  string :=
  match t with BuildTransition  input output  => input end.
Definition Transition_getOutput (t : Transition) :  string :=
  match t with BuildTransition  input output  => output end.


Definition beq_State (st_arg1 : State) (st_arg2 : State) : bool :=
(  beq_string (State_getName st_arg1) (State_getName st_arg2) )
.

Definition beq_Transition (tr_arg1 : Transition) (tr_arg2 : Transition) : bool :=
(  beq_string (Transition_getInput tr_arg1) (Transition_getInput tr_arg2) ) && 
(  beq_string (Transition_getOutput tr_arg1) (Transition_getOutput tr_arg2) )
.


(* Meta-types *)	
Inductive MealyMetamodel_Class : Set :=
  | StateClass
  | TransitionClass
.

Definition MealyMetamodel_getTypeByClass (mecl_arg : MealyMetamodel_Class) : Set :=
  match mecl_arg with
    | StateClass => State
    | TransitionClass => Transition
  end.	

Inductive MealyMetamodel_Reference : Set :=
| TransitionSourceReference
| TransitionTargetReference
.

Definition MealyMetamodel_getTypeByReference (mere_arg : MealyMetamodel_Reference) : Set :=
  match mere_arg with
| TransitionSourceReference => TransitionSource
| TransitionTargetReference => TransitionTarget
  end.

Definition MealyMetamodel_getERoleTypesByEReference (mere_arg : MealyMetamodel_Reference) : Set :=
  match mere_arg with
| TransitionSourceReference => (Transition * State)
| TransitionTargetReference => (Transition * State)
  end.

(* Generic types *)			
Inductive MealyMetamodel_Object : Set :=
 | Build_MealyMetamodel_Object : 
    forall (mecl_arg: MealyMetamodel_Class), (MealyMetamodel_getTypeByClass mecl_arg) -> MealyMetamodel_Object.

Definition beq_MealyMetamodel_Object (c1 : MealyMetamodel_Object) (c2 : MealyMetamodel_Object) : bool :=
  match c1, c2 with
  | Build_MealyMetamodel_Object StateClass o1, Build_MealyMetamodel_Object StateClass o2 => beq_State o1 o2
  | Build_MealyMetamodel_Object TransitionClass o1, Build_MealyMetamodel_Object TransitionClass o2 => beq_Transition o1 o2
  | _, _ => false
  end.

Inductive MealyMetamodel_Link : Set :=
 | Build_MealyMetamodel_Link : 
    forall (mere_arg:MealyMetamodel_Reference), (MealyMetamodel_getTypeByReference mere_arg) -> MealyMetamodel_Link.

(* TODO *)
Definition beq_MealyMetamodel_Link (l1 : MealyMetamodel_Link) (l2 : MealyMetamodel_Link) : bool := true.

(* Reflective functions *)
Lemma MealyMetamodel_eqEClass_dec : 
 forall (mecl_arg1:MealyMetamodel_Class) (mecl_arg2:MealyMetamodel_Class), { mecl_arg1 = mecl_arg2 } + { mecl_arg1 <> mecl_arg2 }.
Proof. repeat decide equality. Defined.

Lemma MealyMetamodel_eqEReference_dec : 
 forall (mere_arg1:MealyMetamodel_Reference) (mere_arg2:MealyMetamodel_Reference), { mere_arg1 = mere_arg2 } + { mere_arg1 <> mere_arg2 }.
Proof. repeat decide equality. Defined.

Definition MealyMetamodel_getEClass (meob_arg : MealyMetamodel_Object) : MealyMetamodel_Class :=
   match meob_arg with
  | (Build_MealyMetamodel_Object meob_arg _) => meob_arg
   end.

Definition MealyMetamodel_getEReference (meli_arg : MealyMetamodel_Link) : MealyMetamodel_Reference :=
   match meli_arg with
  | (Build_MealyMetamodel_Link meli_arg _) => meli_arg
   end.

Definition MealyMetamodel_instanceOfEClass (mecl_arg: MealyMetamodel_Class) (meob_arg : MealyMetamodel_Object): bool :=
  if MealyMetamodel_eqEClass_dec (MealyMetamodel_getEClass meob_arg) mecl_arg then true else false.

Definition MealyMetamodel_instanceOfEReference (mere_arg: MealyMetamodel_Reference) (meli_arg : MealyMetamodel_Link): bool :=
  if MealyMetamodel_eqEReference_dec (MealyMetamodel_getEReference meli_arg) mere_arg then true else false.


Definition MealyMetamodel_toClass (mecl_arg : MealyMetamodel_Class) (meob_arg : MealyMetamodel_Object) : option (MealyMetamodel_getTypeByClass mecl_arg).
Proof.
  destruct meob_arg as [arg1 arg2].
  destruct (MealyMetamodel_eqEClass_dec arg1 mecl_arg) as [e|] eqn:dec_case.
  - rewrite e in arg2.
    exact (Some arg2).
  - exact None.
Defined.

Definition MealyMetamodel_toReference (mere_arg : MealyMetamodel_Reference) (meli_arg : MealyMetamodel_Link) : option (MealyMetamodel_getTypeByReference mere_arg).
Proof.
  destruct meli_arg as [arg1 arg2].
  destruct (MealyMetamodel_eqEReference_dec arg1 mere_arg) as [e|] eqn:dec_case.
  - rewrite e in arg2.
  	exact (Some arg2).
  - exact None.
Defined.

(* Generic functions *)
Definition MealyModel := Model MealyMetamodel_Object MealyMetamodel_Link.

Definition MealyMetamodel_toObject (mecl_arg: MealyMetamodel_Class) (t: MealyMetamodel_getTypeByClass mecl_arg) : MealyMetamodel_Object :=
  (Build_MealyMetamodel_Object mecl_arg t).

Definition MealyMetamodel_toLink (mere_arg: MealyMetamodel_Reference) (t: MealyMetamodel_getTypeByReference mere_arg) : MealyMetamodel_Link :=
  (Build_MealyMetamodel_Link mere_arg t).





Fixpoint Transition_getSourceOnLinks (tr_arg : Transition) (l : list MealyMetamodel_Link) : option (State) :=
match l with
| (Build_MealyMetamodel_Link TransitionSourceReference (BuildTransitionSource Transition_ctr source_ctr)) :: l' => 
	  if beq_Transition Transition_ctr tr_arg then Some source_ctr else Transition_getSourceOnLinks tr_arg l'
| _ :: l' => Transition_getSourceOnLinks tr_arg l'
| nil => None
end.

Definition Transition_getSource (tr_arg : Transition) (m : MealyModel) : option (State) :=
  Transition_getSourceOnLinks tr_arg (@allModelLinks _ _ m).
  
Definition Transition_getSourceObject (tr_arg : Transition) (m : MealyModel) : option (MealyMetamodel_Object) :=
  match Transition_getSource tr_arg m with
  | Some st_arg => Some (MealyMetamodel_toObject StateClass st_arg) 
  | _ => None
  end.
Fixpoint Transition_getTargetOnLinks (tr_arg : Transition) (l : list MealyMetamodel_Link) : option (State) :=
match l with
| (Build_MealyMetamodel_Link TransitionTargetReference (BuildTransitionTarget Transition_ctr target_ctr)) :: l' => 
	  if beq_Transition Transition_ctr tr_arg then Some target_ctr else Transition_getTargetOnLinks tr_arg l'
| _ :: l' => Transition_getTargetOnLinks tr_arg l'
| nil => None
end.

Definition Transition_getTarget (tr_arg : Transition) (m : MealyModel) : option (State) :=
  Transition_getTargetOnLinks tr_arg (@allModelLinks _ _ m).
  
Definition Transition_getTargetObject (tr_arg : Transition) (m : MealyModel) : option (MealyMetamodel_Object) :=
  match Transition_getTarget tr_arg m with
  | Some st_arg => Some (MealyMetamodel_toObject StateClass st_arg) 
  | _ => None
  end.


(* Typeclass Instances *)	

#[export]
Instance MealyMetamodel_ElementSum : Sum MealyMetamodel_Object MealyMetamodel_Class :=
{
	denoteSubType := MealyMetamodel_getTypeByClass;
	toSubType := MealyMetamodel_toClass;
	toSumType := MealyMetamodel_toObject;
}.

#[export]
Instance MealyMetamodel_LinkSum : Sum MealyMetamodel_Link MealyMetamodel_Reference :=
{
	denoteSubType := MealyMetamodel_getTypeByReference;
	toSubType := MealyMetamodel_toReference;
	toSumType := MealyMetamodel_toLink;
}.

#[export]
Instance MealyMetamodel_EqDec : EqDec MealyMetamodel_Object := {
    eq_b := beq_MealyMetamodel_Object;
}.

#[export]
Instance MealyMetamodel_Metamodel_Instance : 
	Metamodel :=
{
	ModelElement := MealyMetamodel_Object;
	ModelLink := MealyMetamodel_Link;
}.

#[export]
Instance MealyMetamodel_ModelingMetamodel_Instance : 
	ModelingMetamodel MealyMetamodel_Metamodel_Instance :=
{ 
    elements := MealyMetamodel_ElementSum;
    links := MealyMetamodel_LinkSum; 
}.

(* Useful lemmas *)

Lemma Mealy_invert : 
  forall (mecl_arg: MealyMetamodel_Class) (t1 t2: MealyMetamodel_getTypeByClass mecl_arg), 
    Build_MealyMetamodel_Object mecl_arg t1 = Build_MealyMetamodel_Object mecl_arg t2 -> t1 = t2.
Admitted.
