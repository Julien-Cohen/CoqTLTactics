Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Export core.TraceLink.

(** * Syntax

      In this section, we introduce _one possible_ abstract syntax of the CoqTL transformation engine.  
      ---- *)

Section Syntax.

Context {tc: TransformationConfiguration}.

(** ** Syntactic Componants

        Next, we model syntactic componants of any transformation specification that supported by the CoqTL engine. *)

(** *** OutputPatternUnit *)

Record OutputPatternUnit : Type :=
  buildOutputPatternUnit {

    opu_name : 
      string ; 

    opu_elementExpr :
      nat -> SourceModel -> (list SourceElementType) -> option TargetElementType ; 

    opu_linkExpr :
      list TraceLink -> nat -> SourceModel -> (list SourceElementType) -> TargetElementType -> option (list TargetLinkType)

}.




(** *** Rule *)

Record Rule : Type :=
  buildRule {
      r_name : string ;
      r_guard : SourceModel -> list SourceElementType -> bool ;
      r_iterator : SourceModel -> list SourceElementType -> option nat ;
      r_outputPattern : list OutputPatternUnit
    } .


(** find an output pattern unit in a rule by the given name: *)

Definition Rule_findOutputPatternUnit (r: Rule) (name: string) : option OutputPatternUnit :=
  find (fun (o:OutputPatternUnit) => beq_string name o.(opu_name))
        r.(r_outputPattern).

(** *** Transformation *)

Record Transformation : Type :=
  buildTransformation 
    { arity : nat ;
      rules : list Rule }.

End Syntax.

(* begin hide *)
Arguments Transformation {_}.
Arguments buildTransformation {_}.

Arguments Rule {_}.
Arguments buildRule {_}.

Arguments buildOutputPatternUnit {_}.
(* end hide *)


(** *** Some tactics to unfold accessors *)

Ltac simpl_r_accessors H :=
  match type of H with 
  | context[
        r_name (buildRule _ _ _ _)] =>
      unfold r_name in H
                                
  | context[
        r_guard (buildRule _ _ _ _)] =>
      unfold r_guard in H
                                 
  | context[
        r_iterator (buildRule _ _ _ _)] =>
      unfold r_iterator in H
                                    
  | context[
        r_outputPattern (buildRule _ _ _ _)] =>
      unfold r_outputPattern in H
                                         
  end.


Ltac simpl_opu_accessors H :=
  match type of H with 
  | context[
        opu_name (buildOutputPatternUnit _ _ _)] =>
      unfold opu_name in H
  | context[
        opu_elementExpr (buildOutputPatternUnit _ _ _)] =>
      unfold opu_elementExpr in H
  | context[
        opu_linkExpr (buildOutputPatternUnit _ _ _)] =>
      unfold opu_linkExpr in H
  end.

