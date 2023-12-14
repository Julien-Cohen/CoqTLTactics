From core 
  Require Certification.

Import 
  NotationUtils String TransformationConfiguration Resolve.

Theorem tr_resolve_leaf {tc : TransformationConfiguration}: 
  forall (tls:list PoorTraceLink.TraceLink)  (name: string)
    (sp: InputPiece) (x: TargetElementType),
    resolve tls name sp = return x ->
    In {| PoorTraceLink.source := (sp, 0, name) ; PoorTraceLink.produced := x |} tls. 
Proof.
  intros ; apply Certification.tr_resolveIter_leaf ; assumption.
Qed.
