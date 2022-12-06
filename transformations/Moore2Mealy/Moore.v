

(********************************************************************
	@name Coq declarations for metamodel: <Moore>
	@date 2022/01/29 12:14:47
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

From core Require Import 
  utils.Utils
  Metamodel
  modeling.ModelingMetamodel
  Model
  utils.CpdtTactics
  Tactics.

(* Base types *)


Inductive State : Set :=
  BuildState :
  (* name *)  string ->
  (* output *)  string ->
  State.

Inductive Transition : Set :=
  BuildTransition :
  (* input *)  string ->
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
  match s with BuildState  name output  => name end.
Definition State_getOutput (s : State) :  string :=
  match s with BuildState  name output  => output end.

Definition Transition_getInput (t : Transition) :  string :=
  match t with BuildTransition  input  => input end.


Definition beq_State (st_arg1 : State) (st_arg2 : State) : bool :=
(  beq_string (State_getName st_arg1) (State_getName st_arg2) ) && 
(  beq_string (State_getOutput st_arg1) (State_getOutput st_arg2) )
.

Definition beq_Transition (tr_arg1 : Transition) (tr_arg2 : Transition) : bool :=
(  beq_string (Transition_getInput tr_arg1) (Transition_getInput tr_arg2) )
.


(* Meta-types *)	
Inductive MooreMetamodel_Class : Set :=
  | StateClass
  | TransitionClass
.

Definition MooreMetamodel_getTypeByClass (mocl_arg : MooreMetamodel_Class) : Set :=
  match mocl_arg with
    | StateClass => State
    | TransitionClass => Transition
  end.	

Inductive MooreMetamodel_Reference : Set :=
| TransitionSourceReference
| TransitionTargetReference
.

Definition MooreMetamodel_getTypeByReference (more_arg : MooreMetamodel_Reference) : Set :=
  match more_arg with
| TransitionSourceReference => TransitionSource
| TransitionTargetReference => TransitionTarget
  end.

Definition MooreMetamodel_getERoleTypesByEReference (more_arg : MooreMetamodel_Reference) : Set :=
  match more_arg with
| TransitionSourceReference => (Transition * State)
| TransitionTargetReference => (Transition * State)
  end.

(* Generic types *)			
Inductive MooreMetamodel_Object : Set :=
 | Build_MooreMetamodel_Object : 
    forall (mocl_arg: MooreMetamodel_Class), (MooreMetamodel_getTypeByClass mocl_arg) -> MooreMetamodel_Object.

Definition beq_MooreMetamodel_Object (c1 : MooreMetamodel_Object) (c2 : MooreMetamodel_Object) : bool :=
  match c1, c2 with
  | Build_MooreMetamodel_Object StateClass o1, Build_MooreMetamodel_Object StateClass o2 => beq_State o1 o2
  | Build_MooreMetamodel_Object TransitionClass o1, Build_MooreMetamodel_Object TransitionClass o2 => beq_Transition o1 o2
  | _, _ => false
  end.

Inductive MooreMetamodel_Link : Set :=
 | Build_MooreMetamodel_Link : 
    forall (more_arg:MooreMetamodel_Reference), (MooreMetamodel_getTypeByReference more_arg) -> MooreMetamodel_Link.

(* FIXME *)
Definition beq_MooreMetamodel_Link (l1 : MooreMetamodel_Link) (l2 : MooreMetamodel_Link) : bool := true.

(* Reflective functions *)
Lemma MooreMetamodel_eqEClass_dec : 
 forall (mocl_arg1:MooreMetamodel_Class) (mocl_arg2:MooreMetamodel_Class), { mocl_arg1 = mocl_arg2 } + { mocl_arg1 <> mocl_arg2 }.
Proof. repeat decide equality. Defined.

Lemma MooreMetamodel_eqEReference_dec : 
 forall (more_arg1:MooreMetamodel_Reference) (more_arg2:MooreMetamodel_Reference), { more_arg1 = more_arg2 } + { more_arg1 <> more_arg2 }.
Proof. repeat decide equality. Defined.

Definition MooreMetamodel_getEClass (moob_arg : MooreMetamodel_Object) : MooreMetamodel_Class :=
   match moob_arg with
  | (Build_MooreMetamodel_Object moob_arg _) => moob_arg
   end.

Definition MooreMetamodel_getEReference (moli_arg : MooreMetamodel_Link) : MooreMetamodel_Reference :=
   match moli_arg with
  | (Build_MooreMetamodel_Link moli_arg _) => moli_arg
   end.

Definition MooreMetamodel_instanceOfEClass (mocl_arg: MooreMetamodel_Class) (moob_arg : MooreMetamodel_Object): bool :=
  if MooreMetamodel_eqEClass_dec (MooreMetamodel_getEClass moob_arg) mocl_arg then true else false.

Definition MooreMetamodel_instanceOfEReference (more_arg: MooreMetamodel_Reference) (moli_arg : MooreMetamodel_Link): bool :=
  if MooreMetamodel_eqEReference_dec (MooreMetamodel_getEReference moli_arg) more_arg then true else false.


Definition MooreMetamodel_toClass (mocl_arg : MooreMetamodel_Class) (moob_arg : MooreMetamodel_Object) : option (MooreMetamodel_getTypeByClass mocl_arg).
Proof.
  destruct moob_arg as [arg1 arg2].
  destruct (MooreMetamodel_eqEClass_dec arg1 mocl_arg) as [e|] eqn:dec_case.
  - rewrite e in arg2.
    exact (Some arg2).
  - exact None.
Defined.

Definition MooreMetamodel_toReference (more_arg : MooreMetamodel_Reference) (moli_arg : MooreMetamodel_Link) : option (MooreMetamodel_getTypeByReference more_arg).
Proof.
  destruct moli_arg as [arg1 arg2].
  destruct (MooreMetamodel_eqEReference_dec arg1 more_arg) as [e|] eqn:dec_case.
  - rewrite e in arg2.
  	exact (Some arg2).
  - exact None.
Defined.

(* Generic functions *)

Definition MooreMetamodel_Metamodel_Instance : 
  Metamodel :=
  {|
    ModelElement := MooreMetamodel_Object;
    ModelLink := MooreMetamodel_Link;
    elements_eqdec := beq_MooreMetamodel_Object ;
    links_eqdec := beq_MooreMetamodel_Link
  |}.


Definition MooreModel := Model MooreMetamodel_Metamodel_Instance.

Definition MooreMetamodel_toObject (mocl_arg: MooreMetamodel_Class) (t: MooreMetamodel_getTypeByClass mocl_arg) : MooreMetamodel_Object :=
  (Build_MooreMetamodel_Object mocl_arg t).

Definition MooreMetamodel_toLink (more_arg: MooreMetamodel_Reference) (t: MooreMetamodel_getTypeByReference more_arg) : MooreMetamodel_Link :=
  (Build_MooreMetamodel_Link more_arg t).





Fixpoint Transition_getSourceOnLinks (tr_arg : Transition) (l : list MooreMetamodel_Link) : option (State) :=
match l with
| (Build_MooreMetamodel_Link TransitionSourceReference (BuildTransitionSource Transition_ctr source_ctr)) :: l' => 
	  if beq_Transition Transition_ctr tr_arg then Some source_ctr else Transition_getSourceOnLinks tr_arg l'
| _ :: l' => Transition_getSourceOnLinks tr_arg l'
| nil => None
end.

Definition Transition_getSource (tr_arg : Transition) (m : MooreModel) : option (State) :=
  Transition_getSourceOnLinks tr_arg m.(modelLinks).
  
Definition Transition_getSourceObject (tr_arg : Transition) (m : MooreModel) : option (MooreMetamodel_Object) :=
  match Transition_getSource tr_arg m with
  | Some st_arg => Some (MooreMetamodel_toObject StateClass st_arg) 
  | _ => None
  end.
Fixpoint Transition_getTargetOnLinks (tr_arg : Transition) (l : list MooreMetamodel_Link) : option (State) :=
match l with
| (Build_MooreMetamodel_Link TransitionTargetReference (BuildTransitionTarget Transition_ctr target_ctr)) :: l' => 
	  if beq_Transition Transition_ctr tr_arg then Some target_ctr else Transition_getTargetOnLinks tr_arg l'
| _ :: l' => Transition_getTargetOnLinks tr_arg l'
| nil => None
end.

Definition Transition_getTarget (tr_arg : Transition) (m : MooreModel) : option (State) :=
  Transition_getTargetOnLinks tr_arg m.(modelLinks).
  
Definition Transition_getTargetObject (tr_arg : Transition) (m : MooreModel) : option (MooreMetamodel_Object) :=
  match Transition_getTarget tr_arg m with
  | Some st_arg => Some (MooreMetamodel_toObject StateClass st_arg) 
  | _ => None
  end.


(* Typeclass Instances *)	
#[export]
Instance MooreMetamodel_ElementSum : Sum MooreMetamodel_Object MooreMetamodel_Class :=
{
	denoteSubType := MooreMetamodel_getTypeByClass;
	toSubType := MooreMetamodel_toClass;
	toSumType := MooreMetamodel_toObject;
}.

#[export]
Instance MooreMetamodel_LinkSum : Sum MooreMetamodel_Link MooreMetamodel_Reference :=
{
	denoteSubType := MooreMetamodel_getTypeByReference;
	toSubType := MooreMetamodel_toReference;
	toSumType := MooreMetamodel_toLink;
}.


#[export]
Instance MooreMetamodel_ModelingMetamodel_Instance : 
	ModelingMetamodel MooreMetamodel_Metamodel_Instance :=
{ 
    elements := MooreMetamodel_ElementSum;
    links := MooreMetamodel_LinkSum; 
}.

(* Useful lemmas *)

Lemma Moore_invert : 
  forall (mocl_arg: MooreMetamodel_Class) (t1 t2: MooreMetamodel_getTypeByClass mocl_arg), 
    Build_MooreMetamodel_Object mocl_arg t1 = Build_MooreMetamodel_Object mocl_arg t2 -> t1 = t2.
Proof.
  intros. Tactics.dep_inversion H. assumption.
Qed.
