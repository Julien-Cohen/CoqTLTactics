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

    TraceLink_getSourcePattern: TraceLink -> InputPiece;
    TraceLink_getIteration: TraceLink -> nat;
    TraceLink_getName: TraceLink -> string;
    TraceLink_getTargetElement: TraceLink -> TargetElementType;    

    evalOutputPatternElementExpr: SourceModel -> InputPiece -> nat -> OutputPatternElement -> option TargetElementType;
    evalIteratorExpr: Rule -> SourceModel -> InputPiece -> nat;
    evalOutputPatternLinkExpr: SourceModel -> InputPiece -> TargetElementType -> nat -> list TraceLink -> OutputPatternElement -> option (list TargetLinkType);
    evalGuardExpr: Rule->SourceModel->InputPiece-> bool;
}.
  
Class TransformationEngine (tc: TransformationConfiguration) (ts: TransformationSyntax tc) :=
  {
    (** ** allTuples *)

    allTuples (tr: Transformation) (sm : SourceModel) :list (InputPiece) :=
      tuples_up_to_n sm.(modelElements) (Transformation_getArity tr);

    (** ** Functions *)
    
    execute: Transformation -> SourceModel -> TargetModel;
    
    matchPattern: Transformation -> SourceModel -> InputPiece -> list Rule;
    matchRuleOnPattern: Rule -> SourceModel -> InputPiece -> bool;

    instantiatePattern: Transformation -> SourceModel -> InputPiece -> list TargetElementType;

    instantiateRuleOnPattern: Rule -> SourceModel -> InputPiece -> list TargetElementType; 

    instantiateIterationOnPattern: Rule -> SourceModel -> InputPiece -> nat -> list TargetElementType;

    instantiateElementOnPattern: OutputPatternElement -> SourceModel -> InputPiece -> nat -> option TargetElementType;
    
    applyPattern: Transformation -> SourceModel -> InputPiece -> list TargetLinkType;

    applyRuleOnPattern: Rule -> Transformation -> SourceModel -> InputPiece -> list TargetLinkType;

    applyIterationOnPattern: Rule -> Transformation -> SourceModel -> InputPiece -> nat -> list TargetLinkType;

    applyElementOnPattern: OutputPatternElement -> Transformation -> SourceModel -> InputPiece -> nat -> list TargetLinkType;
    
    trace: Transformation -> SourceModel -> list TraceLink; 

    resolveAll: forall (tr: list TraceLink) (sm: SourceModel) (name: string)
             (sps: list(InputPiece)) (iter: nat),
        option (list TargetElementType);
    resolve: forall (tr: list TraceLink) (sm: SourceModel) (name: string)
             (sp: InputPiece) (iter : nat), option TargetElementType;

    (** ** Theorems *)

    (** ** allTuples *)

    allTuples_incl:
      forall (sp : InputPiece) (tr: Transformation) (sm: SourceModel), 
        In sp (allTuples tr sm) -> incl sp sm.(modelElements);

    (** ** execute *)

    tr_execute_in_elements :
      forall (tr: Transformation) (sm : SourceModel) (te : TargetElementType),
      In te (execute tr sm).(modelElements) <->
      (exists (sp : InputPiece),
          In sp (allTuples tr sm) /\
          In te (instantiatePattern tr sm sp));

    tr_execute_in_links :
      forall (tr: Transformation) (sm : SourceModel) (tl : TargetLinkType),
        In tl (execute tr sm).(modelLinks) <->
        (exists (sp : InputPiece),
            In sp (allTuples tr sm) /\
            In tl (applyPattern tr sm sp));

    (** ** matchPattern *)

    tr_matchPattern_in :
       forall (tr: Transformation) (sm : SourceModel),
         forall (sp : InputPiece)(r : Rule),
           In r (matchPattern tr sm sp) <->
             In r (Transformation_getRules tr) /\
             matchRuleOnPattern r sm sp = true;

    (** ** matchRuleOnPattern *)

    tr_matchRuleOnPattern_leaf :
    forall (tr: Transformation) (sm : SourceModel) (r: Rule) (sp: InputPiece),
      matchRuleOnPattern r sm sp = evalGuardExpr r sm sp ; 

    (** ** instantiatePattern *)

    tr_instantiatePattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: InputPiece) (te : TargetElementType),
        In te (instantiatePattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In te (instantiateRuleOnPattern r sm sp));

    (** ** instantiateRuleOnPattern *)

    tr_instantiateRuleOnPattern_in :
    forall (r : Rule) (sm : SourceModel) (sp: InputPiece) (te : TargetElementType),
      In te (instantiateRuleOnPattern r sm sp) <->
      (exists (i: nat),
          In i (seq 0 (evalIteratorExpr r sm sp)) /\
          In te (instantiateIterationOnPattern r sm sp i));

   (** ** instantiateIterationOnPattern *)

    tr_instantiateIterationOnPattern_in : 
      forall (r : Rule) (sm : SourceModel) (sp: InputPiece) (te : TargetElementType) (i:nat),
        In te (instantiateIterationOnPattern r sm sp i)
        <->
        (exists (ope: OutputPatternElement),
            In ope (Rule_getOutputPatternElements r) /\ 
            instantiateElementOnPattern ope sm sp i = Some te);

    (** ** instantiateElementOnPattern *)

    tr_instantiateElementOnPattern_leaf:
        forall (o: OutputPatternElement) (sm: SourceModel) (sp: InputPiece) (iter: nat),
          instantiateElementOnPattern o sm sp iter = evalOutputPatternElementExpr sm sp iter o;

    (** ** applyPattern *)

    tr_applyPattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: InputPiece) (tl : TargetLinkType),
        In tl (applyPattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In tl (applyRuleOnPattern r tr sm sp));

    (** ** applyRuleOnPattern *)

    tr_applyRuleOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: InputPiece) (tl : TargetLinkType),
        In tl (applyRuleOnPattern r tr sm sp) <->
        (exists (i: nat),
            In i (seq 0 (evalIteratorExpr r sm sp)) /\
            In tl (applyIterationOnPattern r tr sm sp i));

    (** ** applyIterationOnPattern *)

    tr_applyIterationOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: InputPiece) (tl : TargetLinkType) (i:nat),
        In tl (applyIterationOnPattern r tr sm sp i) <->
        (exists (ope: OutputPatternElement),
            In ope (Rule_getOutputPatternElements r) /\ 
            In tl (applyElementOnPattern ope tr sm sp i));

    (** ** applyElementOnPattern *)

    tr_applyElementOnPattern_leaf : 
      forall (tr: Transformation) (sm : SourceModel) (sp: InputPiece) (te: TargetElementType) 
             (i:nat) (ope: OutputPatternElement),
        evalOutputPatternElementExpr sm sp i ope = Some te ->
        applyElementOnPattern ope tr sm sp i = optionListToList (evalOutputPatternLinkExpr sm sp te i (trace tr sm) ope);

    (** ** resolve *)

    tr_resolveAll_in:
    forall (tls: list TraceLink) (sm: SourceModel) (name: string)
           (sps: list(InputPiece)) (iter: nat)
      (te: TargetElementType),
      (exists tes: list TargetElementType,
          resolveAll tls sm name sps iter = Some tes /\ In te tes) <->
      (exists (sp: InputPiece),
          In sp sps /\
          resolve tls sm name sp iter = Some te);

    tr_resolve_leaf:
    forall (tls:list TraceLink) (sm : SourceModel) (name: string)
      (sp: InputPiece) (iter: nat) (x: TargetElementType),
      resolve tls sm name sp iter = return x ->
       (exists (tl : TraceLink),
         In tl tls /\
         Is_true (list_beq SourceElement_eqb (TraceLink_getSourcePattern tl) sp) /\
         ((TraceLink_getIteration tl) = iter) /\ 
         ((TraceLink_getName tl) = name)%string /\
         (TraceLink_getTargetElement tl) = x);
         
  }.

Theorem tr_execute_rule_in :
      forall (tc: TransformationConfiguration) (ts: TransformationSyntax tc) (eng: TransformationEngine ts) 
      (tr: Transformation) (sm : SourceModel) (te : TargetElementType),
      In te (execute tr sm).(modelElements) <->
      (exists (sp : InputPiece) (r : Rule),
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
      (exists (sp : InputPiece) (r : Rule) (i: nat),
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
      (exists (sp : InputPiece) (r : Rule) (i: nat) (ope: OutputPatternElement),
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
      (exists (sp : InputPiece) (r : Rule) (i: nat) (ope: OutputPatternElement),
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
