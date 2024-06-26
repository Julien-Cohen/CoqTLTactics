Require Import Semantics.

Import String List Utils.
Import core.PoorTraceLink core.TransformationConfiguration.


(** * User read access in traces ([resolve]) *)

Section Resolve.

Context {tc: TransformationConfiguration}.

Definition resolveIter (tls: Trace) (name: string)
            (sp: InputPiece)
            (iter : nat) : option TargetElementType :=
  option_map PoorTraceLink.produced (find (source_compare (sp,iter,name)) tls) .

Definition resolve (tr: Trace)  (name: string)
  (sp: InputPiece) : option TargetElementType :=
  resolveIter tr name sp 0.


Definition resolveAllIter (tr: Trace) (name: string)
  (sps: list(InputPiece)) (iter: nat)
  : option (list TargetElementType) :=
  Some (flat_map (fun l:(InputPiece) => optionToList (resolveIter tr name l iter)) sps).

Definition resolveAll (tr: Trace) (name: string)
  (sps: list(InputPiece)) : option (list TargetElementType) :=
  resolveAllIter tr name sps 0.




End Resolve.




