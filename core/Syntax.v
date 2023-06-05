Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Export core.PoorTraceLink.

(** * Syntax

      In this section, we introduce _one possible_ abstract syntax of the CoqTL transformation engine.  
      ---- *)

Section Syntax.

Context {tc: TransformationConfiguration}.

(** ** Syntactic Components

        Next, we model syntactic components of any transformation specification that is supported by the CoqTL engine. *)

(** *** OutputPatternUnit *)

Record OutputPatternUnit : Type :=
  buildOutputPatternUnit {

    opu_name : 
      string ; 

    opu_element :
      nat -> SourceModel -> InputPiece -> option TargetElementType ; 

    opu_link :
      PoorTraceLink.Trace -> nat -> SourceModel -> InputPiece -> TargetElementType -> list TargetLinkType

}.




(** *** Rule *)

Record Rule : Type :=
  buildRule {
      r_name : string ;
      r_guard : SourceModel -> InputPiece -> bool ;
      r_iterator : SourceModel -> InputPiece -> option nat ;
      r_outputPattern : list OutputPatternUnit
    } .


(** Find an output pattern unit in a rule by the given name: *)

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
        opu_element (buildOutputPatternUnit _ _ _)] =>
      unfold opu_element in H
  | context[
        opu_link (buildOutputPatternUnit _ _ _)] =>
      unfold opu_link in H
  end.

