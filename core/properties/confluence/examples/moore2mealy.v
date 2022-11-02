Require Import String.
Require Import EqNat.
Require Import List.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.


Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.properties.confluence.basic.basicExpressions.
Require Import core.properties.confluence.basic.basicSemantics.
Require Import core.properties.confluence.basic.basicSyntax.
Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.Certification.
Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import transformations.Moore2Mealy.Moore.
Require Import transformations.Moore2Mealy.Mealy.

Require Import core.properties.confluence.confluence.
Require Import core.properties.confluence.examples.moore2mealy_confluence.

(*************************************************************)
(** * Confluence of CoqTL                                    *)
(*************************************************************)

(** directly instantiate Confluence on Moore2Mealy           *)


Theorem confluence :
forall  (sm: MooreModel),
   TargetModel_equiv (execute Moore2Mealy sm) (execute Moore2Mealy2 sm).
Proof.
intros.
assert (Transformation_equiv Moore2Mealy Moore2Mealy2).
{
unfold Transformation_equiv.
split.
- simpl. auto.
- split. 
  -- unfold set_eq.
     simpl.
     remember (buildRule "transition"
    (fun (_ : SourceModel) (_ : list SourceModelElement) =>
    return true)
    (fun (_ : SourceModel) (_ : list SourceModelElement) =>
    return 1) nil) as r1.
     remember (buildRule "state"
    (fun (_ : SourceModel) (_ : list SourceModelElement) =>
      return true)
    (fun (_ : SourceModel) (_ : list SourceModelElement) =>
      return 1) nil) as r2.
      crush.
  -- split; simpl; unfold well_form; crush.
}
apply confluence.
exact H.
Qed.

