From Stdlib 
  Require Import String EqNat List PeanoNat Lia FunctionalExtensionality.

From core 
  Require Import Semantics Syntax Model TransformationConfiguration utils.Utils.

From core 
  Require Certification.

From core.modeling
  Require Import ConcreteSyntax ModelingSemantics ModelingMetamodel ConcreteExpressions Parser.


(*************************************************************)
(** * Backward_Traceability of CoqTL (Element)               *)
(** * Using operational semantics                            *)
(*************************************************************)

(** intuitively: I do not create from scratch target elements, a.k.a.
                 it does not exist a situation where a target element is not connected to any source pattern*)

Definition Backward_Traceability_elem {tc: TransformationConfiguration}  (tr: Transformation) : Prop := 
    forall (sm : SourceModel) (te : TargetElementType),
    In te (execute tr sm).(modelElements) ->
    (exists (sp : InputPiece),
        In sp (allTuples tr sm) /\
        In te (produced_elements (traceTrOnPiece tr sm sp))).


Theorem forall_Backward_Traceability_elem {tc:TransformationConfiguration} :
forall (tr: Transformation), Backward_Traceability_elem tr.
Proof.
    unfold Backward_Traceability_elem.
    apply Certification.tr_execute_in_elements.
Qed.

(* Future Work : consider to use prop in AxiomaticSemantics *)
    

