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



Definition outputPatternLink
(skinds : list SourceEKind) (tkind: TargetEKind)  (tref: TargetLKind):=
denoteSignature skinds ((denoteEDatatype tkind) -> option (denoteLDatatype tref)).



Definition outputPatternElementTypes
(skinds : list SourceEKind) (tkind: TargetEKind) :=
  denoteSignature skinds (denoteEDatatype tkind).



Record ConcreteOutputPatternLink (InKinds: list SourceEKind) (OutKind:TargetEKind) : Type :=
  link 
    {
      o_OutRefKind: TargetLKind ;
      o_outpat : list TraceLink -> nat -> SourceModel -> (outputPatternLink InKinds OutKind o_OutRefKind)
    }.

Global Arguments o_OutRefKind {_ _}.
Global Arguments o_outpat {_ _}.


Record ConcreteOutputPatternElement (InKinds: list SourceEKind) : Type :=
  elem
    {
      e_OutKind:TargetEKind ;
      e_name : string ;
      e_outpat : nat -> SourceModel -> (outputPatternElementTypes InKinds e_OutKind) ;
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
      r_outpat : list (ConcreteOutputPatternElement r_InKinds)
    }.

Inductive ConcreteTransformation : Type :=
  transformation :
    list ConcreteRule
    -> ConcreteTransformation.

(** ** Accessors **)


Definition ConcreteRule_findConcreteOutputPatternElement (r: ConcreteRule) (name: string) : option (ConcreteOutputPatternElement (r_InKinds r)) :=
  find (fun(o:ConcreteOutputPatternElement r.(r_InKinds) ) => beq_string name o.(e_name))
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
Notation "'rule' rulename 'from' types 'where' guard 'to' [ 'ELEM' n ::: t << op >>  ]" :=
  (Build_ConcreteRule rulename types (Some guard) None [ elem types t n op nil ])
    (right associativity, at level 60):coqtl.


(* Rule : 0 iterator, 1 guard, 1 link *)
Notation "'rule' rulename 'from' types 'where' guard 'to' [ 'ELEM' n ::: t << op >> <<< 'LINK' c // d >>> ]" :=
  (Build_ConcreteRule rulename types (Some guard) None [ elem types t n op [link types t c d] ])
    (right associativity, at level 60):coqtl.

(* Rule : 0 iterator, 1 guard, 2 links *)
Notation "'rule' rulename 'from' types 'where' guard 'to' [ 'ELEM' n ::: t << op >> <<< 'LINK' c // d ; 'LINK' e // f >>> ]" :=
  (Build_ConcreteRule rulename types (Some guard) None [ elem types t n op [link types t c d ; link types t e f] ])
    (right associativity, at level 60):coqtl.


(* Rule : 0 iterator, 0 guard, 0 link *)
Notation "'rule' rulename 'from' types 'to' [ 'ELEM' n ::: t << op >> ]" :=
  (Build_ConcreteRule rulename types None None [ elem types t n op nil ])
    (right associativity, at level 60):coqtl.


(* Rule : 0 iterator, 0 guard, 1 link *)
Notation "'rule' rulename 'from' types 'to' [ 'ELEM' n ::: t << op >> <<< 'LINK' c // d >>> ]" :=
  (Build_ConcreteRule rulename types None None [ elem types t n op [link types t c d] ])
    (right associativity, at level 60):coqtl.


(* Rule : 0 iterator, 0 guard, 2 links *)
Notation "'rule' rulename 'from' types 'to' [ 'ELEM' n ::: t << op >> <<< 'LINK' c // d ; 'LINK' e // f >>> ]" :=
  (Build_ConcreteRule rulename types None None [ elem types t n op [link types t c d ; link types t e f] ])
    (right associativity, at level 60):coqtl.

(* We need the separators above.

The following, without a separator, does not work.

Notation "'A' [ i j ]" := (i + j).
Definition Truc := A [ 1 2 ] . 

The following, with a separator, works.

Notation "'A' [ i | j ]" := (i + j).

Definition Truc := A [ 1 | 2 ] . 
*)
