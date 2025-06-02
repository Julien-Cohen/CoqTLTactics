From core.properties.backward_traceability 
  Require Import backward_traceability_elem backward_traceability_link.

Import TransformationConfiguration Syntax.

Theorem Backward_Traceability {tc:TransformationConfiguration} :
    forall (tr: Transformation), Backward_Traceability_elem tr /\ Backward_Traceability_link tr.
Proof.
  intro tr ; split ; [ apply forall_Backward_Traceability_elem | apply forall_Backward_Traceability_links ].
Qed.