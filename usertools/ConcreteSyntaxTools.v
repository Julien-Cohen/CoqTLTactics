(** Some hints to unfold accessors of ConcreteSyntax types. *)

Require Import ConcreteSyntax.

#[global]
Hint Unfold 
  o_OutRefKind 
  o_outpat : ConcreteOutputPatternLink_accessors.

#[global]
Hint Unfold 
  r_name 
  r_InKinds 
  r_guard 
  r_iter 
  r_outpat : ConcreteRule_accessors.

#[global]
Hint Unfold 
  e_OutKind 
  e_name 
  e_outpat 
  e_outlink : ConcreteOutputPatternUnit_accessors.
