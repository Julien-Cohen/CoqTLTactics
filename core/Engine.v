(************************************************************************)
(*         *   The NaoMod Development Team                              *)
(*  v      *   INRIA, CNRS and contributors - Copyright 2017-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**
 This file is the type class for relational transformation engine.
 
 We give functions signatures that instaniated transformation engines should
    generally have. We also introduce several useful theorems enforced on these 
    functions in order to certify instaniated transformation engines.

 An example instaniated transformation engine is in [core.Certification].        **)


(*********************************************************)
(** * Type Class for relational Transformation Engines   *)
(*********************************************************)

Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.

Scheme Equality for list.

Set Implicit Arguments.

Class TransformationSyntax (tc: TransformationConfiguration) := {
    (** ** Syntax *)
    Transformation: Type;
    Rule: Type;
    OutputPatternElement: Type;
    TraceLink: Type;

    (** ** Accessors *)

    Transformation_getRules: Transformation -> list Rule;
    Transformation_getArity: Transformation -> nat;
  
    Rule_getOutputPatternElements: Rule -> list OutputPatternElement;

    TraceLink_getSourcePattern: TraceLink -> list SourceElementType;
    TraceLink_getIteration: TraceLink -> nat;
    TraceLink_getName: TraceLink -> string;
    TraceLink_getTargetElement: TraceLink -> TargetElementType;    

    evalOutputPatternElementExpr: SourceModel -> list SourceElementType -> nat -> OutputPatternElement -> option TargetElementType;
    evalIteratorExpr: Rule -> SourceModel -> list SourceElementType -> nat;
    evalOutputPatternLinkExpr: SourceModel -> list SourceElementType -> TargetElementType -> nat -> list TraceLink -> OutputPatternElement -> option (list TargetLinkType);
    evalGuardExpr: Rule->SourceModel->list SourceElementType-> bool;
}.
  
Class TransformationEngine (tc: TransformationConfiguration) (ts: TransformationSyntax tc) :=
  {
    (** ** allTuples *)

    allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceElementType) :=
      tuples_up_to_n sm.(modelElements) (Transformation_getArity tr);

    (** ** Functions *)
    
    execute: Transformation -> SourceModel -> TargetModel;
    
    matchPattern: Transformation -> SourceModel -> list SourceElementType -> list Rule;
    matchRuleOnPattern: Rule -> SourceModel -> list SourceElementType -> bool;

    instantiatePattern: Transformation -> SourceModel -> list SourceElementType -> list TargetElementType;

    instantiateRuleOnPattern: Rule -> SourceModel -> list SourceElementType -> list TargetElementType; 

    instantiateIterationOnPattern: Rule -> SourceModel -> list SourceElementType -> nat -> list TargetElementType;

    instantiateElementOnPattern: OutputPatternElement -> SourceModel -> list SourceElementType -> nat -> option TargetElementType;
    
    applyPattern: Transformation -> SourceModel -> list SourceElementType -> list TargetLinkType;

    applyRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceElementType -> list TargetLinkType;

    applyIterationOnPattern: Rule -> Transformation -> SourceModel -> list SourceElementType -> nat -> list TargetLinkType;

    applyElementOnPattern: OutputPatternElement -> Transformation -> SourceModel -> list SourceElementType -> nat -> list TargetLinkType;
    
    trace: Transformation -> SourceModel -> list TraceLink; 

    resolveAll: forall (tr: list TraceLink) (sm: SourceModel) (name: string)
             (sps: list(list SourceElementType)) (iter: nat),
        option (list TargetElementType);
    resolve: forall (tr: list TraceLink) (sm: SourceModel) (name: string)
             (sp: list SourceElementType) (iter : nat), option TargetElementType;

    (** ** Theorems *)

    (** ** allTuples *)

    allTuples_incl:
      forall (sp : list SourceElementType) (tr: Transformation) (sm: SourceModel), 
        In sp (allTuples tr sm) -> incl sp sm.(modelElements);

    (** ** execute *)

    tr_execute_in_elements :
      forall (tr: Transformation) (sm : SourceModel) (te : TargetElementType),
      In te (execute tr sm).(modelElements) <->
      (exists (sp : list SourceElementType),
          In sp (allTuples tr sm) /\
          In te (instantiatePattern tr sm sp));

    tr_execute_in_links :
      forall (tr: Transformation) (sm : SourceModel) (tl : TargetLinkType),
        In tl (execute tr sm).(modelLinks) <->
        (exists (sp : list SourceElementType),
            In sp (allTuples tr sm) /\
            In tl (applyPattern tr sm sp));

    (** ** matchPattern *)

    tr_matchPattern_in :
       forall (tr: Transformation) (sm : SourceModel),
         forall (sp : list SourceElementType)(r : Rule),
           In r (matchPattern tr sm sp) <->
             In r (Transformation_getRules tr) /\
             matchRuleOnPattern r sm sp = true;

    (** ** matchRuleOnPattern *)

    tr_matchRuleOnPattern_leaf :
    forall (tr: Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceElementType),
      matchRuleOnPattern r sm sp = evalGuardExpr r sm sp ; 

    (** ** instantiatePattern *)

    tr_instantiatePattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) (te : TargetElementType),
        In te (instantiatePattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In te (instantiateRuleOnPattern r sm sp));

    (** ** instantiateRuleOnPattern *)

    tr_instantiateRuleOnPattern_in :
    forall (r : Rule) (sm : SourceModel) (sp: list SourceElementType) (te : TargetElementType),
      In te (instantiateRuleOnPattern r sm sp) <->
      (exists (i: nat),
          In i (seq 0 (evalIteratorExpr r sm sp)) /\
          In te (instantiateIterationOnPattern r sm sp i));

   (** ** instantiateIterationOnPattern *)

    tr_instantiateIterationOnPattern_in : 
      forall (r : Rule) (sm : SourceModel) (sp: list SourceElementType) (te : TargetElementType) (i:nat),
        In te (instantiateIterationOnPattern r sm sp i)
        <->
        (exists (ope: OutputPatternElement),
            In ope (Rule_getOutputPatternElements r) /\ 
            instantiateElementOnPattern ope sm sp i = Some te);

    (** ** instantiateElementOnPattern *)

    tr_instantiateElementOnPattern_leaf:
        forall (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceElementType) (iter: nat),
          instantiateElementOnPattern o sm sp iter = evalOutputPatternElementExpr sm sp iter o;

    (** ** applyPattern *)

    tr_applyPattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) (tl : TargetLinkType),
        In tl (applyPattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In tl (applyRuleOnPattern r tr sm sp));

    (** ** applyRuleOnPattern *)

    tr_applyRuleOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceElementType) (tl : TargetLinkType),
        In tl (applyRuleOnPattern r tr sm sp) <->
        (exists (i: nat),
            In i (seq 0 (evalIteratorExpr r sm sp)) /\
            In tl (applyIterationOnPattern r tr sm sp i));

    (** ** applyIterationOnPattern *)

    tr_applyIterationOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceElementType) (tl : TargetLinkType) (i:nat),
        In tl (applyIterationOnPattern r tr sm sp i) <->
        (exists (ope: OutputPatternElement),
            In ope (Rule_getOutputPatternElements r) /\ 
            In tl (applyElementOnPattern ope tr sm sp i));

    (** ** applyElementOnPattern *)

    tr_applyElementOnPattern_leaf : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) (te: TargetElementType) 
             (i:nat) (ope: OutputPatternElement),
        evalOutputPatternElementExpr sm sp i ope = Some te ->
        applyElementOnPattern ope tr sm sp i = optionListToList (evalOutputPatternLinkExpr sm sp te i (trace tr sm) ope);

    (** ** resolve *)

    tr_resolveAll_in:
    forall (tls: list TraceLink) (sm: SourceModel) (name: string)
           (sps: list(list SourceElementType)) (iter: nat)
      (te: TargetElementType),
      (exists tes: list TargetElementType,
          resolveAll tls sm name sps iter = Some tes /\ In te tes) <->
      (exists (sp: list SourceElementType),
          In sp sps /\
          resolve tls sm name sp iter = Some te);

    tr_resolve_leaf:
    forall (tls:list TraceLink) (sm : SourceModel) (name: string)
      (sp: list SourceElementType) (iter: nat) (x: TargetElementType),
      resolve tls sm name sp iter = return x ->
       (exists (tl : TraceLink),
         In tl tls /\
         Is_true (list_beq SourceElementType SourceElement_eqb (TraceLink_getSourcePattern tl) sp) /\
         ((TraceLink_getIteration tl) = iter) /\ 
         ((TraceLink_getName tl) = name)%string /\
         (TraceLink_getTargetElement tl) = x);
         
  }.

Theorem tr_execute_rule_in :
      forall (tc: TransformationConfiguration) (ts: TransformationSyntax tc) (eng: TransformationEngine ts) 
      (tr: Transformation) (sm : SourceModel) (te : TargetElementType),
      In te (execute tr sm).(modelElements) <->
      (exists (sp : list SourceElementType) (r : Rule),
          In sp (allTuples tr sm) /\
          In r (Transformation_getRules tr) /\
          matchRuleOnPattern r sm sp = true /\
          In te (instantiateRuleOnPattern r sm sp)).
Proof.
  intros.
  rewrite tr_execute_in_elements. 
  split.
  * intros. repeat destruct H. 
    apply tr_instantiatePattern_in in H0.
    repeat destruct H0. 
    apply tr_matchPattern_in in H0.
    exists x, x0.
    crush.
  * intros. repeat destruct H. destruct H0, H1.
    exists x.
    crush.
    apply tr_instantiatePattern_in.
    exists x0.
    crush.
    apply tr_matchPattern_in.
    crush.
Qed.

Theorem tr_execute_iteration_in :
      forall (tc: TransformationConfiguration) (ts: TransformationSyntax tc) (eng: TransformationEngine ts) 
      (tr: Transformation) (sm : SourceModel) (te : TargetElementType),
      In te (execute tr sm).(modelElements) <->
      (exists (sp : list SourceElementType) (r : Rule) (i: nat),
          In sp (allTuples tr sm) /\
          In r (Transformation_getRules tr) /\
          matchRuleOnPattern r sm sp = true /\
          In i (seq 0 (evalIteratorExpr r sm sp)) /\
          In te (instantiateIterationOnPattern r sm sp i)).
Proof.
  intros.
  rewrite tr_execute_rule_in.
  split.
  * intros. repeat destruct H. destruct H0, H1.
    apply tr_instantiateRuleOnPattern_in in H2.
    destruct H2.
    exists x, x0, x1.
    crush.
  * intros. repeat destruct H. destruct H0, H1, H2.
    exists x, x0.
    crush.
    apply tr_instantiateRuleOnPattern_in.
    exists x1.
    crush.
Qed.
  
Theorem tr_execute_element_in :
      forall (tc: TransformationConfiguration) (ts: TransformationSyntax tc) (eng: TransformationEngine ts) 
      (tr: Transformation) (sm : SourceModel) (te : TargetElementType),
      In te (execute tr sm).(modelElements) <->
      (exists (sp : list SourceElementType) (r : Rule) (i: nat) (ope: OutputPatternElement),
          In sp (allTuples tr sm) /\
          In r (Transformation_getRules tr) /\
          matchRuleOnPattern r sm sp = true /\
          In i (seq 0 (evalIteratorExpr r sm sp)) /\
          In ope (Rule_getOutputPatternElements r) /\ 
          instantiateElementOnPattern ope sm sp i = Some te).
Proof.
  intros.
  rewrite tr_execute_iteration_in.
  split.
  * intros. repeat destruct H. destruct H0, H1, H2.
    apply tr_instantiateIterationOnPattern_in in H3.
    destruct H3.
    exists x, x0, x1, x2.
    crush.
  * intros. repeat destruct H. destruct H0, H1, H2, H3.
    exists x, x0, x1.
    crush.
    apply tr_instantiateIterationOnPattern_in.
    exists x2.
    crush.
Qed.

Theorem tr_execute_element_leaf :
      forall (tc: TransformationConfiguration) (ts: TransformationSyntax tc) (eng: TransformationEngine ts) 
      (tr: Transformation) (sm : SourceModel) (te : TargetElementType),
      In te (execute tr sm).(modelElements) <->
      (exists (sp : list SourceElementType) (r : Rule) (i: nat) (ope: OutputPatternElement),
          In sp (allTuples tr sm) /\
          In r (Transformation_getRules tr) /\
          evalGuardExpr r sm sp = true /\
          In i (seq 0 (evalIteratorExpr r sm sp)) /\
          In ope (Rule_getOutputPatternElements r) /\ 
          evalOutputPatternElementExpr sm sp i ope = Some te).
Proof.
  intros.
  rewrite tr_execute_element_in.
  split.
  * intros. repeat destruct H. destruct H0, H1, H2, H3.
    rewrite tr_matchRuleOnPattern_leaf in H1. 
    rewrite tr_instantiateElementOnPattern_leaf in H4.
    exists x, x0, x1, x2.
    crush. crush. 
  * intros. repeat destruct H. destruct H0, H1, H2, H3.
    exists x, x0, x1, x2.
    crush.
    rewrite tr_matchRuleOnPattern_leaf. assumption.
    crush. crush. 
    rewrite tr_instantiateElementOnPattern_leaf.
    crush.
Qed.

(* TODO: similar for links *)
