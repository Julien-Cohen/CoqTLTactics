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
    match (toEKind sc se) with
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

Definition denoteOutput (type: TargetEKind) (f: option TargetModelElement): option (denoteEKind type) :=
    match f with
    | Some e => toEKind type e
    | _ => None
    end.

Definition denoteOutputList (type: TargetEKind) (f: option (list TargetModelElement)): option (list (denoteEKind type)) :=
    match f with
    | Some l => Some (flat_map (fun e:TargetModelElement => optionToList (toEKind type e)) l)
    | _ => None
    end.


Definition resolveIter (tls: list TraceLink) (sm: SourceModel) (name: string)
            (type: TargetEKind) (sp: list SourceModelElement)
            (iter : nat) : option (denoteEKind type) :=
  denoteOutput type (resolveIter tls sm name sp iter).

Definition resolve (tr: list TraceLink) (sm: SourceModel) (name: string)
  (type: TargetEKind) (sp: list SourceModelElement) : option (denoteEKind type) :=
  denoteOutput type (resolve tr sm name sp).

Definition resolveAllIter (tr: list TraceLink) (sm: SourceModel) (name: string)
  (type: TargetEKind) (sps: list(list SourceModelElement)) (iter: nat)
  : option (list (denoteEKind type)) :=
  denoteOutputList type (resolveAllIter tr sm name sps iter).

Definition resolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
  (type: TargetEKind) (sps: list(list SourceModelElement)) : option (list (denoteEKind type)) :=
  denoteOutputList type (resolveAll tr sm name sps).

Definition maybeResolve (tr: list TraceLink) (sm: SourceModel) (name: string)
  (type: TargetEKind) (sp: option (list SourceModelElement)) : option (denoteEKind type) :=
  denoteOutput type (maybeResolve tr sm name sp).

Definition maybeResolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
  (type: TargetEKind) (sp: option (list (list SourceModelElement))) : option (list (denoteEKind type)) :=
  denoteOutputList type (maybeResolveAll tr sm name sp).

End SemanticsModeling.
