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

(** ** Syntax **)

Fixpoint denoteFunction (sclasses : list SourceModelClass) (otype: Type) :=
  match sclasses with
  | nil => otype
  | cons class classes' => (denoteModelClass class) -> denoteFunction classes' otype
  end.

Definition outputPatternLink
(sclasses : list SourceModelClass) (tclass: TargetModelClass)  (tref: TargetModelReference):=
denoteFunction (sclasses) ((denoteModelClass tclass) -> option (denoteModelReference tref)).

Definition outputPatternElementTypes
(sclasses : list SourceModelClass) (tclass: TargetModelClass) :=
  denoteFunction (sclasses) (denoteModelClass tclass).

Definition iteratedListTypes
(sclasses : list SourceModelClass) :=
  denoteFunction (sclasses) nat.

Definition guardTypes (sclasses : list SourceModelClass) :=
  denoteFunction (sclasses) bool.

Record ConcreteOutputPatternLink (InTypes: list SourceModelClass) (OutType:TargetModelClass) : Type :=
  link 
    {
      o_OutRef: TargetModelReference ;
      o_outpat : list TraceLink -> nat -> SourceModel -> (outputPatternLink InTypes OutType o_OutRef)
    }.

Global Arguments o_OutRef {_ _}.
Global Arguments o_outpat {_ _}.

Record ConcreteOutputPatternElement (InTypes: list SourceModelClass) : Type :=
  elem
    {
      e_OutType:TargetModelClass ;
      e_name : string ;
      e_outpat : nat -> SourceModel -> (outputPatternElementTypes InTypes e_OutType) ;
      e_outlink : list (ConcreteOutputPatternLink InTypes e_OutType)
    }.

Global Arguments e_name {_}.
Global Arguments e_OutType {_}.
Global Arguments e_outpat {_}. 
Global Arguments e_outlink {_}. 


Record ConcreteRule  :=
    { 
      r_name : string ;
      r_InTypes: list SourceModelClass ;
      r_guard :  option (SourceModel -> (guardTypes r_InTypes)) ;
      r_iter :  option (SourceModel -> (iteratedListTypes r_InTypes)) ;
      r_outpat   :  (list (ConcreteOutputPatternElement r_InTypes))
    }.

Inductive ConcreteTransformation : Type :=
  transformation :
    list ConcreteRule
    -> ConcreteTransformation.

(** ** Accessors **)


Definition ConcreteRule_findConcreteOutputPatternElement (r: ConcreteRule) (name: string) : option (ConcreteOutputPatternElement (r_InTypes r)) :=
  find (fun(o:ConcreteOutputPatternElement r.(r_InTypes) ) => beq_string name o.(e_name))
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
