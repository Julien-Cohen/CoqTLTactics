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
    (* id *) string 
    (* element expr *) -> (nat -> SourceModel -> (list SourceElementType) -> option TargetElementType) 
    (* link expr *) -> ((SourceModel -> string -> list SourceElementType -> nat -> option TargetElementType) 
                         -> nat -> SourceModel -> (list SourceElementType) -> TargetElementType -> option (list TargetLinkType)) -> OutputPatternElement.
 
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

Inductive Rule : Type :=
  buildRule :
    (* name *) string
    (* from *) -> (SourceModel -> (list SourceElementType) -> option bool)
    (* for *) -> (SourceModel -> (list SourceElementType) -> option nat)
    (* to *) -> (list OutputPatternElement)
    -> Rule.

Definition Rule_getName (x : Rule) : string :=
  match x with
    buildRule y _ _ _ => y
  end.
  
Definition Rule_getGuardExpr (x : Rule) : SourceModel -> (list SourceElementType) -> option bool :=
  match x with
    buildRule _ y _ _ => y
  end.

Definition Rule_getIteratorExpr (x : Rule) : SourceModel -> (list SourceElementType) -> option nat :=
  match x with
    buildRule _ _ y _ => y
  end.

Definition Rule_getOutputPatternElements (x : Rule) :
  list OutputPatternElement :=
  match x with
    buildRule _ _ _ y => y
  end.

(** find an output pattern element in a rule by the given name: *)

Definition Rule_findOutputPatternElement (r: Rule) (name: string) : option OutputPatternElement :=
  find (fun (o:OutputPatternElement) => beq_string name (OutputPatternElement_getName o))
        (Rule_getOutputPatternElements r).

(** *** Transformation *)

Inductive Transformation : Type :=
  buildTransformation :
    nat
    -> list Rule
    -> Transformation.

Definition Transformation_getArity (x : Transformation) : nat :=
  match x with buildTransformation y _ => y end.

Definition Transformation_getRules (x : Transformation) : list Rule :=
  match x with buildTransformation _ y => y end.

End Syntax.

(* begin hide *)
Arguments Transformation {_}.
Arguments buildTransformation {_}.

Arguments Rule {_}.
Arguments buildRule {_}.

Arguments buildOutputPatternElement {_}.
(* end hide *)
