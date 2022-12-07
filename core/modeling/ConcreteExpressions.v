Require Import String.

Require Import core.utils.Utils.
Require Import core.Syntax.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Section ConcreteExpressions.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.  

(** ** Generic functions generation *)

(** Convert a list of kinds into a function type. *)
(** Example : [denoteSignature [A;B;C] D = a -> b -> c -> d .] *) 
Fixpoint denoteSignature (l : list SourceEKind) (r : Type) : Type :=
  match l with
  | nil => r
  | k :: l' => denoteEDatatype k -> denoteSignature l' r
  end.


Fixpoint wrapOption 
  {T : Type} 
  (l : list SourceEKind) 
  (imp : denoteSignature l T)
  (sl : list SourceModelElement) {struct l} : 
  option T :=
  match (l,sl) 
        as l0 
        return (denoteSignature (fst l0) T -> option T) with
    
  | (nil,nil) => (fun v : denoteSignature nil T => Some v)
                 
  | (k :: rk, e::re) =>
      fun (f : denoteSignature (k :: rk) T) =>
        match toEData k e with
        | Some x => wrapOption (T:=T) rk (f x) re
        | None => None 
        end

  | (_::_, nil) => (fun _ => None)
  
  | (nil, _::_) => (fun _ => None) 
          
  end imp
.
(** Example : wrapOption D [k1;k2;k3] (f := fun a b c => d) [C1 e1 ; C2 e2 ; C3 e3] = Some (f e1 e2 e3) *)
(** Example : wrapOption D [k1;k2;k3] (f := fun a b c => d) [C1 e1 ; C2 e2 ] = None *)
(** Example : wrapOption D [k1;k2;k3] (f := fun a b c => d) [C1 e1; C2 e2 ;C4 e2] = None (k3 and C4 do not match) *)


Remark wrapOption_len :
  forall t l1 (D:denoteSignature l1 t) l2,
    length l1 <> length l2 ->
    wrapOption l1 D l2 = None.
Proof.
  induction l1 ; intros D l2 L ; destruct l2.
  { contradict L ; reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { simpl.
    destruct (toEData a s).
    + apply IHl1. contradict L. simpl. congruence.
    + reflexivity.
  }
Qed.

Notation instanceof := mtc.(smm).(elements).(instanceof).

Fixpoint wrapOption' (l:list SourceEKind) (sl : list SourceModelElement) : bool :=
  match (l, sl) with
  | (nil, nil) => true
  | (k1::r1, e2::r2) => instanceof k1 e2 && wrapOption' r1 r2 
  | (nil , _ :: _) => false
  | (_::_ , nil) => false
  end. 


Remark wrapOption'_len :
  forall l1  l2,
    length l1 <> length l2 ->
    wrapOption' l1 l2 = false.
Proof.
  induction l1 ; intros l2 L ; destruct l2.
  { contradict L ; reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { simpl.
    destruct (instanceof a s).
    + apply IHl1. contradict L. simpl. congruence.
    + reflexivity.
  }
Qed.

Definition wrapList {T : Type} (l : list SourceEKind)
  (imp : denoteSignature l (list T)) :
  (list SourceModelElement) -> list T.
Proof.
  revert l imp. fix Hl 1. intros l imp sl.
  destruct l as [ | l0 l'], sl as [ | s0 sl'].
  - exact imp.
  - exact nil.
  - exact nil.
  - destruct (toEData l0 s0) as [x | ].
    + exact (Hl l' (imp x) sl').
    + exact nil.
Defined.



Definition wrapOptionElement
  (l : list SourceEKind) (k : TargetEKind)
  (imp : denoteSignature l (denoteEDatatype k)) :
  (list SourceModelElement) -> option TargetModelElement.
Proof.
  revert l imp. fix Hl 1. intros l imp sl.
  destruct l as [ | l0 l'], sl as [ | s0 sl'].
  - exact (Some (toModelElement k imp)).
  - exact None.
  - exact None.
  - exact (x0 <- toEData l0 s0; Hl l' (imp x0) sl').
Defined.

Definition wrapOptionLink
  (l : list SourceEKind) (k : TargetEKind) (r : TargetLKind)
  (imp : denoteSignature l (denoteEDatatype k -> option (denoteLDatatype r))) :
  (list SourceModelElement) -> TargetModelElement -> option (list TargetModelLink).
Proof.
  revert l imp. fix Hl 1. intros l imp sl v.
  destruct l as [ | l0 l'], sl as [ | s0 sl'].
  - refine (xv <- toEData k v; xr <- imp xv; return [toModelLink r xr]).
  - exact None.
  - exact None.
  - exact (x0 <- toEData l0 s0; Hl l' (imp x0) sl' v).
Defined.

Definition GuardFunction : Type :=
  SourceModel -> (list SourceModelElement) -> bool.

(* BEGIN FIXME *)
Definition drop_option_to_bool a :=
  match a with
  | None => false
  | Some b => b
  end.

Definition makeGuard 
  (l : list SourceEKind)
  (imp : SourceModel -> denoteSignature l bool) :
  GuardFunction :=
  fun sm => fun s => drop_option_to_bool (wrapOption l (imp sm) s).
(* END FIXME *)

Definition makeEmptyGuard (l : list SourceEKind) : GuardFunction :=
  fun sm => wrapOption' l.

Definition IteratorFunction : Type :=
  SourceModel -> (list SourceModelElement) -> option nat.

Definition makeIterator (l : list SourceEKind)
  (imp : SourceModel -> denoteSignature l nat) :
  IteratorFunction :=
  fun sm => wrapOption l (imp sm).

Definition ElementFunction : Type :=
  nat -> SourceModel -> (list SourceModelElement) -> option TargetModelElement.

Definition makeElement (l : list SourceEKind) (k : TargetEKind)
  (imp : nat -> SourceModel -> denoteSignature l (denoteEDatatype k)) :
  ElementFunction :=
  fun it sm => wrapOptionElement l k (imp it sm).

Definition LinkFunction : Type :=
  list TraceLink
  -> nat -> SourceModel -> (list SourceModelElement) -> TargetModelElement -> option (list TargetModelLink).

Definition makeLink (l : list SourceEKind) (k : TargetEKind) (r : TargetLKind)
  (imp : list TraceLink -> nat -> SourceModel -> denoteSignature l (denoteEDatatype k -> option (denoteLDatatype r))) :
  LinkFunction :=
  fun mt it sm => wrapOptionLink l k r (imp mt it sm).

End ConcreteExpressions.
