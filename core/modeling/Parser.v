Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.ConcreteSyntax.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

(* parse Concrete syntax into abstract syntax. *)

Local Notation SourceEKind := smmm.(EKind).
Local Notation TargetEKind := tmmm.(EKind).

Section Parser.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.

Definition parseOutputPatternLink (inkinds: list SourceEKind) (outtype: TargetEKind)
  (cr: ConcreteOutputPatternLink inkinds outtype) := 
    (makeLink inkinds outtype cr.(o_OutRefKind) cr.(o_outpat)).

Definition parseOutputPatternLinks (inkinds: list SourceEKind) (outtype: TargetEKind)
  (cr: list (ConcreteOutputPatternLink inkinds outtype)) := 
    fun (tls:list TraceLink) (iter:nat) (sm:SourceModel) (sp: list SourceElementType) (te: TargetElementType) =>
    Some (flat_map (fun (x: ConcreteOutputPatternLink inkinds outtype) => optionListToList (parseOutputPatternLink inkinds outtype x tls iter sm sp te)) cr).

Definition dropToList : 
  (list TraceLink -> nat -> SourceModel -> InputPiece -> TargetElementType -> option (list TargetLinkType) )
  -> (list TraceLink -> nat -> SourceModel -> InputPiece -> TargetElementType -> list TargetLinkType ) 
  := fun f => (fun a b c d e => optionListToList (f a b c d e)).
  
Definition parseOutputPatternUnit (inkinds: list SourceEKind) (co: ConcreteOutputPatternElement inkinds) : OutputPatternUnit :=
  buildOutputPatternUnit
    co.(e_name)
    (makeElement inkinds co.(e_OutKind) co.(e_outpat))
    (dropToList (parseOutputPatternLinks inkinds co.(e_OutKind) co.(e_outlink))).

Definition parseRule(cr: ConcreteRule) : Rule :=
  buildRule
    cr.(r_name)
    ( match cr.(r_guard) with
      | Some g => (makeGuard cr.(r_InKinds) g)
      | None => (makeEmptyGuard cr.(r_InKinds))
      end
    )
    ( match cr.(r_iter) with
      | Some i => (makeIterator cr.(r_InKinds) i)
      | None => (fun _ _ => Some 1)
      end
    )
    ( map (parseOutputPatternUnit cr.(r_InKinds)) cr.(r_outpat) ).

Definition parse(ct: ConcreteTransformation) : Transformation :=
  buildTransformation 
    (max (map (length (A:=SourceEKind)) (map r_InKinds (ConcreteTransformation_getConcreteRules ct))))
    (map parseRule (ConcreteTransformation_getConcreteRules ct)).

End Parser.

(** Some tactics. *)

Ltac unfold_parseRule H:=
  unfold parseRule in H ; 
  unfold parseOutputPatternUnit in H ; 
  unfold parseOutputPatternLinks in H ; 
  unfold parseOutputPatternLink in H.
