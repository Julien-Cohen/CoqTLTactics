(************************************************************************)
(*         *   The NaoMod Development Team                              *)
(*  v      *   INRIA, CNRS and contributors - Copyright 2017-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**
 This file is the type class for relational transformation engine.
 
 We give functions signatures that instaniated transformation engines should
    generally have. We also introduce several useful theorems enforced on these 
    functions in order to certify instaniated transformation engines.

 An example instaniated transformation engine is in [core.Certification].        **)


(*********************************************************)
(** * Type Class for relational Transformation Engines   *)
(*********************************************************)

Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Engine.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Scheme Equality for list.

Set Implicit Arguments.

Class ModelingTransformationEngine (tc: TransformationConfiguration) (mtc: ModelingTransformationConfiguration tc) (ts: TransformationSyntax tc)
  (t: TransformationEngine ts) :=
  {
    resolveAll: forall (tr: list TraceLink) (sm: SourceModel) (name: string)
             (type: TargetEKind) (sps: list(list SourceModelElement)) (iter: nat),
        option (list (denoteEKind type));
    resolve: forall (tr: list TraceLink) (sm: SourceModel) (name: string)
             (type: TargetEKind) (sp: list SourceModelElement) (iter : nat), option (denoteEKind type);

    (** ** Theorems *)

    tr_resolveAll_in:
    forall (tls: list TraceLink) (sm: SourceModel) (name: string)
      (type: TargetEKind) (sps: list(list SourceModelElement)) (iter: nat)
      (te: denoteEKind type),
      (exists tes: list (denoteEKind type),
          resolveAll tls sm name type sps iter = Some tes /\ In te tes) <->
      (exists (sp: list SourceModelElement),
          In sp sps /\
          resolve tls sm name type sp iter = Some te);

    tr_resolve_leaf:
    forall (tls:list TraceLink) (sm : SourceModel) (name: string) (type: TargetEKind)
      (sp: list SourceModelElement) (iter: nat) (x: denoteEKind type),
      resolve tls sm name type sp iter = return x ->
       (exists (tl : TraceLink),
         In tl tls /\
         Is_true (list_beq SourceModelElement SourceElement_eqb (TraceLink_getSourcePattern tl) sp) /\
         ((TraceLink_getIterator tl) = iter) /\ 
         ((TraceLink_getName tl) = name)%string /\
         (toEKind type (TraceLink_getTargetElement tl) = Some x));

  }.
