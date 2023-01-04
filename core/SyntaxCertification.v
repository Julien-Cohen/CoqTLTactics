Require Import core.Engine.
Require Import core.Syntax.
Require Import core.TransformationConfiguration.
Require Import core.Expressions.

Section SyntaxCertification.

Context {tc: TransformationConfiguration}.

Instance CoqTLSyntax :
  TransformationSyntax tc :=
  {
      (* syntax and accessors *)

      Transformation := Transformation;
      Rule := Rule;
      OutputPatternElement := OutputPatternElement;

      TraceLink := TraceLink;

      Transformation_getArity := arity;
      Transformation_getRules := rules;

      Rule_getOutputPatternElements := r_outputPattern;

      TraceLink_getSourcePattern := TraceLink_getSourcePattern;
      TraceLink_getIteration := TraceLink_getIteration;
      TraceLink_getName := TraceLink_getName;
      TraceLink_getTargetElement := target ;    
      
      evalOutputPatternElementExpr := evalOutputPatternElementExpr;
      evalIteratorExpr := evalIteratorExpr;
      evalOutputPatternLinkExpr := evalOutputPatternLinkExpr;
      evalGuardExpr := Syntax.r_guard;
  }.

End SyntaxCertification.
