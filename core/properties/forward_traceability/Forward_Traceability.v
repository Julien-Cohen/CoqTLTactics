From core.properties.forward_traceability 
  Require Import Forward_Traceability_elem Forward_Traceability_link.

Import TransformationConfiguration Syntax.

Theorem Forward_Traceability {tc:TransformationConfiguration} :
    forall (tr: Transformation), Forward_Traceability_elem tr /\ Forward_Traceability_links tr.
Proof.
  intro tr ; split ; [ apply forall_Forward_Traceability_elem | apply forall_Forward_Traceability_links ].
Qed.