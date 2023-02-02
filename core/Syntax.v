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

Record OutputPatternElement : Type :=
  buildOutputPatternElement {

    ope_name : 
      string ; 

    ope_elementExpr :
      nat -> SourceModel -> (list SourceElementType) -> option TargetElementType ; 

    ope_linkExpr :
      list TraceLink -> nat -> SourceModel -> (list SourceElementType) -> TargetElementType -> option (list TargetLinkType)

}.




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
  find (fun (o:OutputPatternElement) => beq_string name o.(ope_name))
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


Ltac simpl_ope_accessors H :=
  match type of H with 
  | context[
        ope_name (buildOutputPatternElement _ _ _)] =>
      unfold ope_name in H
  | context[
        ope_elementExpr (buildOutputPatternElement _ _ _)] =>
      unfold ope_elementExpr in H
  | context[
        ope_linkExpr (buildOutputPatternElement _ _ _)] =>
      unfold ope_linkExpr in H
  end.

