Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import core.modeling.ConcreteExpressions.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Section ConcreteSyntax.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.

Local Notation SourceEKind := smmm.(EKind).
Local Notation TargetEKind := tmmm.(EKind).
Local Notation TargetLKind := tmmm.(LKind).


(** ** Syntax (computed types) **)



Definition outputPatternLink (skinds : list SourceEKind) (tkind: TargetEKind)  (tref: TargetLKind):=
  denoteSignature skinds ((denoteEDatatype tkind) -> option (denoteLDatatype tref)).






Record ConcreteOutputPatternLink (InKinds: list SourceEKind) (OutKind:TargetEKind) : Type :=
  link 
    {
      o_OutRefKind: TargetLKind ;
      o_outpat : Trace -> nat -> SourceModel -> (outputPatternLink InKinds OutKind o_OutRefKind)
    }.

Global Arguments o_OutRefKind {_ _}.
Global Arguments o_outpat {_ _}.


Record ConcreteOutputPatternUnit (InKinds: list SourceEKind) : Type :=
  elem
    {
      e_OutKind: TargetEKind ;
      e_name : string ;
      e_outpat : nat -> SourceModel -> denoteSignature InKinds (option (denoteEDatatype e_OutKind)) ;
      e_outlink : list (ConcreteOutputPatternLink InKinds e_OutKind)
    }.

Global Arguments e_name {_}.
Global Arguments e_OutKind {_}.
Global Arguments e_outpat {_}. 
Global Arguments e_outlink {_}. 


Record ConcreteRule  :=
    { 
      r_name   : string ;
      r_InKinds: list SourceEKind ;
      r_guard  : option (SourceModel -> (denoteSignature r_InKinds bool)) ;
      r_iter   : option (SourceModel -> (denoteSignature r_InKinds nat))  ;
      r_outpat : list (ConcreteOutputPatternUnit r_InKinds)
    }.

Inductive ConcreteTransformation : Type :=
  transformation :
    list ConcreteRule
    -> ConcreteTransformation.

(** ** Accessors **)


Definition ConcreteRule_findConcreteOutputPatternUnit (r: ConcreteRule) (name: string) : option (ConcreteOutputPatternUnit (r_InKinds r)) :=
  find (fun(o:ConcreteOutputPatternUnit r.(r_InKinds) ) => beq_string name o.(e_name))
        r.(r_outpat).

Definition ConcreteTransformation_getConcreteRules (x : ConcreteTransformation) : list ConcreteRule :=
  match x with transformation y => y end.

End ConcreteSyntax.

Arguments transformation {_ _}.
Arguments Build_ConcreteRule {_ _}.
Arguments elem {_ _}.
Arguments link {_ _}.

Declare Scope coqtl.

(* Rule *)
Notation "'rule' rulename 'from' types 'where' guard 'for' iterator 'to' outputpattern " :=
  (Build_ConcreteRule rulename types (Some guard) (Some iterator) outputpattern)
    (right associativity, at level 60):coqtl.

(* Rule without guard *)
Notation "'rule' rulename 'from' types 'for' iterator 'to' outputpattern " :=
  (Build_ConcreteRule rulename types (None) (Some iterator) outputpattern)
    (right associativity, at level 60):coqtl.

(* Rule without iterator *)
Notation "'rule' rulename 'from' types 'where' guard 'to' outputpattern " :=
  (Build_ConcreteRule rulename types (Some guard) (None) outputpattern)
    (right associativity, at level 60):coqtl.

(* Rule without guard and iterator *)
Notation "'rule' rulename 'from' types 'to' outputpattern " :=
  (Build_ConcreteRule rulename types (None) (None) outputpattern)
    (right associativity, at level 60):coqtl.


(* Rule : 0 iterator, 1 guard, 0 link *)
Notation "'rule' rulename 'from' types 'where' guard 'to' [ 'ELEM' k ::: t << op >>  ]" :=
  (Build_ConcreteRule rulename types (Some guard) None [ elem types t k op nil ])
    (right associativity, at level 60):coqtl.


(* Rule : 0 iterator, 1 guard, 1 link *)
Notation "'rule' rulename 'from' types 'where' guard 'to' [ 'ELEM' k ::: t << op >> 'LINK' ::: k1 << oplink >> ]" :=
  (Build_ConcreteRule rulename types (Some guard) None [ elem types t k op [link types t k1 oplink] ])
    (right associativity, at level 60):coqtl.

(* Rule : 0 iterator, 1 guard, 2 links *)
Notation "'rule' rulename 'from' types 'where' guard 'to' [ 'ELEM' k ::: t << op >> 'LINK' ::: k1 << oplink1 >> ; 'LINK' ::: k2 << oplink2 >> ]" :=
  (Build_ConcreteRule rulename types (Some guard) None [ elem types t k op [link types t k1 oplink1 ; link types t k2 oplink2] ])
    (right associativity, at level 60):coqtl.


(* Rule : 0 iterator, 0 guard, 0 link *)
Notation "'rule' rulename 'from' types 'to' [ 'ELEM' k ::: t << op >> ]" :=
  (Build_ConcreteRule rulename types None None [ elem types t k op nil ])
    (right associativity, at level 60):coqtl.


(* Rule : 0 iterator, 0 guard, 1 link *)
Notation "'rule' rulename 'from' types 'to' [ 'ELEM' k ::: t << op >> 'LINK' ::: k1 << oplink >> ]" :=
  (Build_ConcreteRule rulename types None None [ elem types t k op [link types t k1 oplink] ])
    (right associativity, at level 60):coqtl.


(* Rule : 0 iterator, 0 guard, 2 links *)
Notation "'rule' rulename 'from' types 'to' [ 'ELEM' k ::: t << op >> 'LINK' ::: k1 << oplink1 >> ; 'LINK' ::: k2 << oplink2 >> ]" :=
  (Build_ConcreteRule rulename types None None [ elem types t k op [link types t k1 oplink1 ; link types t k2 oplink2] ])
    (right associativity, at level 60):coqtl.

(* We need the separators above.

The following, without a separator, does not work.

Notation "'A' [ i j ]" := (i + j).
Definition Truc := A [ 1 2 ] . 

The following, with a separator, works.

Notation "'A' [ i | j ]" := (i + j).

Definition Truc := A [ 1 | 2 ] . 
*)


(** *** Some tactics to unfold accessors *)

Ltac simpl_link_accessors H :=
  match type of H with 
  | context[
        o_OutRefKind (link _ _ _ _)] =>
      unfold o_OutRefKind in H
  | context[
        o_outpat (link _ _ _ _)] =>
      unfold o_outpat in H
  end.

Ltac simpl_cr_accessors H :=
  match type of H with 
  | context[
        r_name (Build_ConcreteRule _ _ _ _ _)] =>
      unfold r_name in H
                                        
  | context[
        r_InKinds (Build_ConcreteRule _ _ _ _ _)] =>
      unfold r_InKinds in H
                                           
  | context[
        r_guard (Build_ConcreteRule _ _ _ _ _)] =>
      unfold r_guard in H
                                         
  | context[
        r_iter (Build_ConcreteRule _ _ _ _ _)] =>
      unfold r_iter in H
                                        
  | context[
        r_outpat (Build_ConcreteRule _ _ _ _ _)] =>
      unfold r_outpat in H
  end.

Ltac simpl_elem_accessors H :=
  match type of H with 
  | context[
        e_OutKind (elem _ _ _ _ _)] =>
      unfold e_OutKind in H
  | context[
        e_name (elem _ _ _ _ _)] =>
      unfold e_name in H
  | context[
        e_outpat (elem _ _ _ _ _)] =>
      unfold e_outpat in H
  | context[
        e_outlink (elem _ _ _ _ _)] =>
      unfold e_outlink in H
  end.
