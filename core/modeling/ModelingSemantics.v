Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.modeling.ConcreteSyntax.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.modeling.Parser.
Require Import Bool.
Require Import Arith.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.
Scheme Equality for list.

Section SemanticsModeling.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.  

(*Fixpoint checkTypes (ses: list SourceModelElement) (scs: list SourceEKind) : bool :=
  match ses, scs with
  | se::ses', sc::scs' => 
    match (toEData sc se) with
    | Some c => checkTypes ses' scs'
    | _ => false
    end
  | nil, nil => true
  | _, _ => false
  end.*)

(*Definition evalGuardExpr (r : ConcreteRule (smm:=smm)) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
  if (checkTypes sp (ConcreteRule_getInTypes (smm:=smm) r)) then
    @evalGuardExpr' SourceModelElement SourceModelLink TargetModelElement TargetModelLink (parseRule r) sm sp
  else Some false. *)

(* ** Resolve *)

(*Definition TraceLink' := @TraceLink SourceModelElement TargetModelElement.*)

Local Notation TargetEKind := tmm.(EKind).

Definition denoteOutput (k: TargetEKind) (f: option TargetModelElement): option (denoteEDatatype k) :=
    match f with
    | Some e => toEData k e
    | _ => None
    end.

Definition denoteOutputList (k: TargetEKind) (f: option (list TargetModelElement)): option (list (denoteEDatatype k)) :=
    match f with
    | Some l => Some (flat_map (fun e:TargetModelElement => optionToList (toEData k e)) l)
    | _ => None
    end.


Definition resolveIter (tls: list TraceLink) (sm: SourceModel) (name: string)
            (k: TargetEKind) (sp: list SourceModelElement)
            (iter : nat) : option (denoteEDatatype k) :=
  denoteOutput k (resolveIter tls sm name sp iter).

Definition resolve (tr: list TraceLink) (sm: SourceModel) (name: string)
  (k: TargetEKind) (sp: list SourceModelElement) : option (denoteEDatatype k) :=
  denoteOutput k (resolve tr sm name sp).

Definition resolveAllIter (tr: list TraceLink) (sm: SourceModel) (name: string)
  (k: TargetEKind) (sps: list(list SourceModelElement)) (iter: nat)
  : option (list (denoteEDatatype k)) :=
  denoteOutputList k (resolveAllIter tr sm name sps iter).

Definition resolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
  (k: TargetEKind) (sps: list(list SourceModelElement)) : option (list (denoteEDatatype k)) :=
  denoteOutputList k (resolveAll tr sm name sps).

Definition maybeResolve (tr: list TraceLink) (sm: SourceModel) (name: string)
  (k: TargetEKind) (sp: option (list SourceModelElement)) : option (denoteEDatatype k) :=
  denoteOutput k (maybeResolve tr sm name sp).

Definition maybeResolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
  (k: TargetEKind) (sp: option (list (list SourceModelElement))) : option (list (denoteEDatatype k)) :=
  denoteOutputList k (maybeResolveAll tr sm name sp).

End SemanticsModeling.
