Require Import core.Engine.
Require Import core.Syntax.
Require Import core.TransformationConfiguration.
Require Import core.UserExpressions.

Section SyntaxCertification.

Context {tc: TransformationConfiguration}.

Instance CoqTLSyntax :
  TransformationSyntax tc :=
  {
      (* syntax and accessors *)

      Transformation := Transformation;
      Rule := Rule;
      OutputPatternElement := OutputPatternUnit;

      TraceLink := TraceLink;

      Transformation_getArity := arity;
      Transformation_getRules := rules;

      Rule_getOutputPatternElements := r_outputPattern;

      TraceLink_getSourcePattern := PoorTraceLink.getSourcePattern;
      TraceLink_getIteration := PoorTraceLink.getIteration;
      TraceLink_getName := PoorTraceLink.getName;
      TraceLink_getTargetElement := produced ;    
      
      evalOutputPatternElementExpr := fun a b c d => evalOutputPatternElement d a b c ; (* change the order of parameters *)
      evalIteratorExpr := evalIterator ;
      evalOutputPatternLinkExpr := fun a b c d e f => Some (evalOutputPatternLink a b c d e f) ;
      evalGuardExpr := Syntax.r_guard;
  }.

End SyntaxCertification.
