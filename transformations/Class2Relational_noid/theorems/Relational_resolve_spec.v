From Stdlib Require Import String.
Require Import Stdlib.Logic.Eqdep_dec.
From Stdlib Require Import Arith.
Require Import Stdlib.Arith.EqNat.
From Stdlib Require Import List.

Require Import core.utils.Utils.
Require Import core.Engine.
Require Import core.TransformationConfiguration.
Require Import core.SyntaxCertification.
Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingEngine.
Require Import core.modeling.ModelingTransformationConfiguration.

Require Import transformations.Class2Relational_noid.Class2Relational.
Require Import transformations.Class2Relational_noid.ClassMetamodel.
Require Import transformations.Class2Relational_noid.RelationalMetamodel.


(* a small example on user proof based on child specification *)

Theorem resolve_trivial:
forall 
  (eng : @TransformationEngine C2RConfiguration CoqTLSyntax)
  (meng: ModelingTransformationEngine Class2RelationalConfiguration eng) 
  (cm : ClassModel) (c: Class_t) tls o,
  (@resolve _ _ _ _ meng tls cm "tab" Table_K [ClassMetamodel.lift_EKind Class_K c] 1) = Some o ->
  (exists (tl : PoorTraceLink.TraceLink), In tl tls).
Proof.
intros.
apply tr_resolve_leaf in H.
destruct H.
destruct H.
exists x.
auto.
Qed.
