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

(** generate function with the convenient type. *) 
Fixpoint dummy {T} (l:list SourceEKind) (n:T) : denoteSignature l T :=
  match l with
  | nil => n
  | k::r => fun e => dummy r n
  end.


Local Notation mismatch := (fun _ => None).

(** [wrap sk impl sl] does typecheck that [sl] has the correct type with respect to [skinds] ans [imp], and if so it applies [imp] to the elements of [sl]. *) 
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


Lemma wrap_inv_nil T b c (e:T) : 
  wrap nil b c  = Some e ->
  b = e /\ c = nil.
Proof.
  destruct c ; simpl. 
  { intro H ; injection H ; intro ; subst ; split ; auto. }
  { intro ; discriminate. }
Qed.

Lemma wrap_inv_nil_nil T b (e:T) : 
  wrap nil b nil  = Some e ->
  b = e .
Proof.
 simpl. 
 intro H ; inj H ; auto. 
Qed.

(* FIXME : move-me *)
Ltac destruct_match :=
  match goal with 
     [ |- context[match ?P with | _ => _ end]] => destruct P eqn:?
  end. 

Lemma wrap_inv_cons T a b c d (e:T) : 
  wrap (cons a b) c d  = Some e ->
  exists a' b' x,
    d = cons a' b' /\ toEData a a' = Some x /\ wrap b (c x) b' = return e.
Proof.
  destruct d ; simpl.
  { intro H ; discriminate H. }
  {
    destruct_match ; simpl.
    {

      intros.  
      eexists ; eexists ; eexists.
      repeat (split ; eauto).
    }
    { intro H ; discriminate H. }
  }
Qed.

Lemma wrap_inv_cons_cons T a b c a' b' (e:T) : 
  wrap (cons a b) c (cons a' b') = Some e ->
  exists x, 
    toEData a a' = Some x /\ wrap b (c x) b' = return e.
Proof.
  simpl.
  destruct_match ; simpl.
  {
    intros.  
    eexists.
    repeat (split ; eauto).
  }
  { intro H ; discriminate H. }
Qed.



Definition drop_option_to_bool a :=
  match a with
  | None => false
  | Some b => b
  end.


Definition wrapElement 
  (skinds : list SourceEKind) 
  (tk : TargetEKind) 
  (imp : denoteSignature skinds (denoteEDatatype tk))
  (selements : list SourceElementType)  :
  option TargetElementType := 

    v <- wrap skinds imp selements ;
    return (elements.(constructor) tk v).

Definition wrapLink
  (skinds : list SourceEKind)
  (k : TargetEKind) 
  (r : TargetLKind) 
  (imp : denoteSignature skinds
           (denoteEDatatype k -> option (denoteLDatatype r)))
  (selements : list SourceElementType)
  (v : TargetElementType) :       
  option (list TargetLinkType) :=

    f <- wrap skinds imp selements ;
    x <- toEData k v ;
    y <- f x ;
    return [links.(constructor) r y].

(** ** Use of those generators *)

Definition GuardFunction : Type :=
  SourceModel -> (list SourceElementType) -> bool.


Definition makeGuard 
  (l : list SourceEKind)
  (imp : SourceModel -> denoteSignature l bool) :
  GuardFunction :=
  fun sm s => drop_option_to_bool (wrap l (imp sm) s).

Definition makeEmptyGuard (l : list SourceEKind) : GuardFunction :=
  fun _ => fun a => drop_option_to_bool (wrap l (dummy l true) a).

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
  Trace
  -> nat -> SourceModel -> (list SourceElementType) -> TargetElementType -> option (list TargetLinkType).

Definition makeLink (l : list SourceEKind) (k : TargetEKind) (r : TargetLKind)
  (imp : Trace -> nat -> SourceModel -> denoteSignature l (denoteEDatatype k -> option (denoteLDatatype r))) :
  LinkFunction :=
  fun mt it sm => wrapLink l k r (imp mt it sm).

End ConcreteExpressions.


Ltac monadInv H :=
  match type of H with
    drop_option_to_bool ?E = true =>
      let b := fresh "b" in
      let TMP := fresh "TMP" in
      assert (TMP : E = Some true) ;
      [ destruct E ; unfold drop_option_to_bool in H ; 
        [ f_equal ; exact H 
        | discriminate H ] 
      | clear H ; rename TMP into H ]

  end.

Ltac exploit_toEData H :=
  match type of H with
  | toEData _ _ = Some ?V =>
      compute in H ; first [ inj H | discriminate H] ; try subst V
  | toEData _ ?e = Some ?V =>
      destruct e ; compute in H ; first [ inj H | discriminate H] ; try subst V
  end.


Ltac dummy_inv H :=
  match type of H with 
    | ConcreteExpressions.dummy _ true _ = true =>
        clear H
  end.

 Ltac wrap_inv H :=
   match type of H with
   | ConcreteExpressions.wrap (cons _ _) _ (cons _ _) = Some (*?V*) _ =>
       let e := fresh "e" in
       let sp := fresh "sp" in 
       let t:= fresh "t" in 
       let T_e := fresh "T_e" in
       apply ConcreteExpressions.wrap_inv_cons_cons in H ;
       destruct H as (t & T_e & H) ; 
       exploit_toEData T_e (*;
       try subst V*)
   | ConcreteExpressions.wrap (cons _ _) _ ?SP = Some (*?V*) _ =>
       let e := fresh "e" in
       let sp := fresh "sp" in 
       let t:= fresh "t" in 
       let T_e := fresh "T_e" in
       apply ConcreteExpressions.wrap_inv_cons in H ;
       destruct H as (e & sp & t & E & T_e & H) ; 
       exploit_toEData T_e ;
       try subst SP  (*;
       try subst V*)
   | ConcreteExpressions.wrap nil _ nil = Some ?V =>
       apply ConcreteExpressions.wrap_inv_nil_nil in H ;
       try first [subst V | inj H | dummy_inv H ]
   | ConcreteExpressions.wrap nil _ ?SP = Some ?V =>
       let E := fresh "E" in 
       apply ConcreteExpressions.wrap_inv_nil in H ;
       destruct H as [H E];
       try subst SP ;
       try first [subst V | inj H | dummy_inv H ]
   end.

Ltac inv_makeElement H := 
  match type of H with
  | makeElement _ _ _ _ _ _ = Some _ =>
      unfold makeElement in H ;
      unfold wrapElement in H ; 
      OptionUtils.monadInv H ;
      try discriminate ;
      repeat wrap_inv H
  end.

Ltac inv_makeGuard H :=
  match type of H with 
  | makeEmptyGuard _ _ _ = true =>
      unfold makeEmptyGuard in H ; 
      monadInv H ;
      repeat wrap_inv H
             
  | makeGuard _ _ _ _  = true => 
      unfold makeGuard in H ;
      monadInv H ;
      repeat wrap_inv H
  
  end.      
  
Ltac inv_makeLink H :=
  match type of H with
  | makeLink _ _ _ _ _ _ _ _ _ = Some _ =>
      unfold makeLink in H ;
      unfold wrapLink in H ; 
      let H2:= fresh "H" in
      match type of H with 
        _ <- ?E ; _ = Some _ => 
          destruct E eqn:H2 ; [ | discriminate H]
      end ;
      repeat ConcreteExpressions.wrap_inv H2 ;
      OptionUtils.monadInv H ;
      OptionUtils.monadInv H
  end.
