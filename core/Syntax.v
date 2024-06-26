Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Export core.PoorTraceLink.

(** * Syntax

      In this section, we introduce _one possible_ abstract syntax of the CoqTL transformation engine.  
      ---- *)


Notation element_producer := 
  (nat -> SourceModel -> InputPiece -> option TargetElementType).

Notation link_producer := 
  (PoorTraceLink.Trace -> nat -> SourceModel -> InputPiece -> TargetElementType -> list TargetLinkType).


Section Syntax.

Context {tc: TransformationConfiguration}.

(** ** Syntactic Components

        Next, we model syntactic components of any transformation specification that is supported by the CoqTL engine. *)

(** *** OutputPatternUnit *)

Record OutputPatternUnit : Type :=
  buildOutputPatternUnit {
      opu_name : string ; 
      opu_element : element_producer ; 
      opu_link : link_producer
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


