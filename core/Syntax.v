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

(** ** Syntactic Elements

        Next, we model syntactic elements of any transformation specification that supported by the CoqTL engine. *)

(** *** OutputPatternElement *)

Inductive OutputPatternElement : Type :=
  buildOutputPatternElement :
    string 
    -> (nat -> SourceModel -> (list SourceElementType) -> option TargetElementType) 
    -> (list TraceLink -> nat -> SourceModel -> (list SourceElementType) -> TargetElementType -> option (list TargetLinkType)) -> OutputPatternElement.

Definition OutputPatternElement_getName (o: OutputPatternElement) : string :=
  match o with
    buildOutputPatternElement y _ _ => y
  end.

Definition OutputPatternElement_getElementExpr (o: OutputPatternElement) : nat -> SourceModel -> (list SourceElementType) -> option TargetElementType :=
  match o with
    buildOutputPatternElement _ y _ => y
  end.

Definition OutputPatternElement_getLinkExpr (o: OutputPatternElement) :=
  match o with
    buildOutputPatternElement _ _ y => y
      end.

(** *** Rule *)

Record Rule : Type :=
  buildRule {
      r_name : string ;
      r_guard : SourceModel -> list SourceElementType -> bool ;
      r_iterator : SourceModel -> list SourceElementType -> option nat ;
      r_outputPattern : list OutputPatternElement
    } .


(** find an output pattern element in a rule by the given name: *)

Definition Rule_findOutputPatternElement (r: Rule) (name: string) : option OutputPatternElement :=
  find (fun (o:OutputPatternElement) => beq_string name (OutputPatternElement_getName o))
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

Arguments buildOutputPatternElement {_}.
(* end hide *)
