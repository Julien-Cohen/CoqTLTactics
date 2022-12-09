Require Import String.

Require Import core.utils.Utils.
Require Import core.Syntax.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Section ConcreteExpressions.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.  

Local Notation SourceEKind := smmm.(EKind).
Local Notation TargetEKind := tmmm.(EKind).
Local Notation TargetLKind := tmmm.(LKind).

(** ** Generic functions generation *)

(** Convert a list of kinds into a function type. *)
(** Example : [denoteSignature [A;B;C] D = a -> b -> c -> d .] *) 
Fixpoint denoteSignature (l : list SourceEKind) (r : Type) : Type :=
  match l with
  | nil => r
  | k :: l' => denoteEDatatype k -> denoteSignature l' r
  end.

Local Notation mismatch := (fun _ => None).

Fixpoint wrap 
  {T : Type} 
  (skinds : list SourceEKind) 
  (imp : denoteSignature skinds T)
  (sl : list SourceElementType) {struct skinds} : 
  option T :=
  match (skinds,sl) 
        as c
        return (denoteSignature (fst c) T -> option T) with
    
  | (nil,nil) => 
      fun v => Some v
                 
  | (k :: rk, e::re) =>
      match toEData k e with
      | Some d => 
          fun f  => wrap rk (f d) re
      
      | None => mismatch
      end

  | (_::_, nil) => mismatch

  
  | (nil, _::_) => mismatch

          
  end imp.
(** Example : wrap [k1;k2;k3] f [C1 e1 ; C2 e2 ; C3 e3] = Some (f e1 e2 e3) (if all the types match) *)
(** Example : wrap [k1;k2;k3] f [C1 e1 ; C2 e2 ] = None *)
(** Example : wrap [k1;k2;k3] f [C1 e1; C2 e2 ;C4 e2] = None (k3 and C4 do not match) *)



Local Notation instanceof := mtc.(smmm).(elements).(instanceof).

(* FIXME : utiliser wrap pour definir wrap' ? *)
Fixpoint wrap' (l:list SourceEKind) (sl : list SourceElementType) : bool :=
  match (l, sl) with
  | (nil, nil) => true
  | (k1::r1, e2::r2) => instanceof k1 e2 && wrap' r1 r2 
  | (nil , _ :: _) => false
  | (_::_ , nil) => false
  end. 






Fixpoint wrapElement 
  (skinds : list SourceEKind) 
  (tk : TargetEKind) 
  (imp : denoteSignature skinds (denoteEDatatype tk))
  (selements : list SourceElementType) {struct skinds} :
  option TargetElementType :=
  match (skinds,selements) as c
        return (denoteSignature (fst c) (denoteEDatatype tk) -> option TargetElementType)
  with

  | (nil, nil) => 
      fun v  => Some (elements.(constructor) tk v)

  | (k::rk, e :: re) =>
      match toEData k e with
      | Some v =>
          fun f => wrapElement rk tk (f v) re

      | None => mismatch 

      end

  | (nil , _ :: _) => mismatch

  | (_ :: _ , nil) => mismatch

                                              
end imp.

Fixpoint wrapLink
  (skinds : list SourceEKind)
  (k : TargetEKind) 
  (r : TargetLKind) 
  (imp : denoteSignature skinds
           (denoteEDatatype k -> option (denoteLDatatype r)))
  (selements : list SourceElementType)
  (v : TargetElementType) {struct skinds}
  :       
  
        option (list TargetLinkType)
:= 

   match (skinds, selements) as c
     return (denoteSignature (fst c) (denoteEDatatype k -> option (denoteLDatatype r)) ->
        option (list TargetLinkType))
   with
     
   | (nil, nil) => 
       match toEData k v with
       | Some d =>
           (fun tr =>  
             t_d <- tr d ; Some [links.(constructor) r t_d])
 
       | None => mismatch
       end
  
                                      
   | (k1 :: rk, e1 :: re) =>
       match toEData k1 e1 with
       | Some d =>
          fun f => wrapLink rk k r (f d) re v

       | None => mismatch

       end

   | (nil , _ :: _) => mismatch
                                     
   | (_ :: _ , nil) => mismatch
                            
   end imp .


(** ** Use of those generators *)

Definition GuardFunction : Type :=
  SourceModel -> (list SourceElementType) -> bool.

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
  fun sm s => drop_option_to_bool (wrap l (imp sm) s).
(* END FIXME *)

Definition makeEmptyGuard (l : list SourceEKind) : GuardFunction :=
  fun _ => wrap' l.

Definition IteratorFunction : Type :=
  SourceModel -> (list SourceElementType) -> option nat.

Definition makeIterator (l : list SourceEKind)
  (imp : SourceModel -> denoteSignature l nat) :
  IteratorFunction :=
  fun sm => wrap l (imp sm).

Definition ElementFunction : Type :=
  nat -> SourceModel -> (list SourceElementType) -> option TargetElementType.

Definition makeElement (l : list SourceEKind) (k : TargetEKind)
  (imp : nat -> SourceModel -> denoteSignature l (denoteEDatatype k)) :
  ElementFunction :=
  fun it sm => wrapElement l k (imp it sm).

Definition LinkFunction : Type :=
  list TraceLink
  -> nat -> SourceModel -> (list SourceElementType) -> TargetElementType -> option (list TargetLinkType).

Definition makeLink (l : list SourceEKind) (k : TargetEKind) (r : TargetLKind)
  (imp : list TraceLink -> nat -> SourceModel -> denoteSignature l (denoteEDatatype k -> option (denoteLDatatype r))) :
  LinkFunction :=
  fun mt it sm => wrapLink l k r (imp mt it sm).

End ConcreteExpressions.
