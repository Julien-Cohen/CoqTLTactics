Require Import Semantics.

Import String List Utils.
Import core.PoorTraceLink core.TransformationConfiguration.


(** * User read access in traces ([resolve]) *)

Section Resolve.

Context {tc: TransformationConfiguration}.

Definition resolveIter (tls: list TraceLink) (name: string)
            (sp: InputPiece)
            (iter : nat) : option TargetElementType :=
  option_map PoorTraceLink.produced (find (source_compare (sp,iter,name)) tls) .

Definition resolve (tr: list TraceLink)  (name: string)
  (sp: InputPiece) : option TargetElementType :=
  resolveIter tr name sp 0.


Definition resolveAllIter (tr: list TraceLink) (name: string)
  (sps: list(InputPiece)) (iter: nat)
  : option (list TargetElementType) :=
  Some (flat_map (fun l:(InputPiece) => optionToList (resolveIter tr name l iter)) sps).

Definition resolveAll (tr: list TraceLink) (name: string)
  (sps: list(InputPiece)) : option (list TargetElementType) :=
  resolveAllIter tr name sps 0.

Definition maybeResolve (tr: list TraceLink) (name: string)
  (sp: option (InputPiece)) : option TargetElementType :=
  sp' <- sp ;
  resolve tr name sp' .


Definition maybeResolveAll (tr: list TraceLink) (name: string)
  (sp: option (list (InputPiece))) : option (list TargetElementType) :=
  sp' <- sp ; 
  resolveAll tr name sp'.


End Resolve.

(** * Some tactics *)

(* tactics need to be outside the section to be visible *)

Ltac inv_maybeResolve H := 
  OptionUtils.monadInvN maybeResolve H.

Ltac inv_maybeResolveAll H := 
  OptionUtils.monadInvN maybeResolveAll H.


Ltac inv_resolve H :=
  match type of H with
  | resolve _ _ _  = Some _ =>
      unfold resolve in H ; 
      OptionUtils.monadInvN resolveIter H
  end.


Ltac progress_maybeResolve H :=
  match type of H with 
    maybeResolve _ _ _  = Some _ =>
      inv_maybeResolve H ;
      inv_resolve H ; 
      apply List.find_some in H ; 
      let N := fresh H in
      destruct H as (H & N)
end.

