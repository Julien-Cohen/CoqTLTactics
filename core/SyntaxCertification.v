Require Import core.Engine.
Require Import core.Syntax.
Require Import core.TransformationConfiguration.
Require Import core.EvalExpressions.

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

      TraceLink_getSourcePattern := TraceLink.getSourcePattern;
      TraceLink_getIteration := TraceLink.getIteration;
      TraceLink_getName := TraceLink.getName;
      TraceLink_getTargetElement := target ;    
      
      evalOutputPatternElementExpr := fun a b c d => evalOutputPatternElementExpr d a b c ; (* change the order of parameters *)
      evalIteratorExpr := evalIteratorExpr;
      evalOutputPatternLinkExpr := evalOutputPatternLinkExpr;
      evalGuardExpr := Syntax.r_guard;
  }.

End SyntaxCertification.
