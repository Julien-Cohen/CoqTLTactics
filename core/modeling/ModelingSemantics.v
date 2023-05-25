Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.modeling.ConcreteSyntax.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Resolve.
Require Import core.modeling.Parser.
Require Import Bool.
Require Import Arith.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.
Scheme Equality for list.

Section SemanticsModeling.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.  


(* ** Resolve *)


Local Notation TargetEKind := tmmm.(EKind).

Definition denoteOutput (k: TargetEKind) (f: option TargetElementType) : option (denoteEDatatype k) := 
  e <- f ; toEData k e.

Definition denoteOutputList (k: TargetEKind) (f: option (list TargetElementType)): option (list (denoteEDatatype k)) :=
  option_map 
    (flat_map (fun e:TargetElementType => optionToList (toEData k e)))
    f.

Definition resolveIter (tls: list TraceLink) (name: string)
            (k: TargetEKind) (sp: list SourceElementType)
            (iter : nat) : option (denoteEDatatype k) :=
  denoteOutput k (Resolve.resolveIter tls name sp iter).

Definition resolve (tr: list TraceLink) (name: string)
  (k: TargetEKind) (sp: list SourceElementType) : option (denoteEDatatype k) :=
  denoteOutput k (Resolve.resolve tr name sp).

Definition resolveAllIter (tr: list TraceLink) (name: string)
  (k: TargetEKind) (sps: list(list SourceElementType)) (iter: nat)
  : option (list (denoteEDatatype k)) :=
  denoteOutputList k (Resolve.resolveAllIter tr name sps iter).

Definition resolveAll (tr: list TraceLink) (name: string)
  (k: TargetEKind) (sps: list(list SourceElementType)) : option (list (denoteEDatatype k)) :=
  denoteOutputList k (Resolve.resolveAll tr name sps).

Definition maybeResolve (tr: list TraceLink) (name: string)
  (k: TargetEKind) (sp: option (list SourceElementType)) : option (denoteEDatatype k) :=
  denoteOutput k (Resolve.maybeResolve tr name sp).

Definition maybeResolveAll (tr: list TraceLink) (name: string)
  (k: TargetEKind) (sp: option (list (list SourceElementType))) : option (list (denoteEDatatype k)) :=
  denoteOutputList k (Resolve.maybeResolveAll tr name sp).

End SemanticsModeling.

Ltac inv_denoteOutput H := monadInvN denoteOutput H.

