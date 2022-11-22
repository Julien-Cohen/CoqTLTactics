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

Section Parser.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.

Definition parseOutputPatternLink (intypes: list SourceModelClass) (outtype: TargetModelClass)
  (cr: ConcreteOutputPatternLink intypes outtype) := 
    (makeLink intypes outtype cr.(o_OutRef) cr.(o_outpat)).

Definition parseOutputPatternLinks (intypes: list SourceModelClass) (outtype: TargetModelClass)
  (cr: list (ConcreteOutputPatternLink intypes outtype)) := 
    fun (tls:list TraceLink) (iter:nat) (sm:SourceModel) (sp: list SourceModelElement) (te: TargetModelElement) =>
    Some (flat_map (fun (x: ConcreteOutputPatternLink intypes outtype) => optionListToList (parseOutputPatternLink intypes outtype x tls iter sm sp te)) cr).

Definition parseOutputPatternElement (intypes: list SourceModelClass) (co: ConcreteOutputPatternElement intypes) : OutputPatternElement :=
  buildOutputPatternElement
    co.(e_name)
    (makeElement intypes co.(e_OutType) co.(e_outpat))
    (parseOutputPatternLinks intypes co.(e_OutType) co.(e_outlink)).

Definition parseRule(cr: ConcreteRule) : Rule :=
  buildRule
    cr.(r_name)
    ( match cr.(r_guard) with
      | Some g => (makeGuard cr.(r_InTypes) g)
      | None => (makeEmptyGuard cr.(r_InTypes))
      end
    )
    ( match cr.(r_iter) with
      | Some i => (makeIterator cr.(r_InTypes) i)
      | None => (fun _ _ => Some 1)
      end
    )
    ( map (parseOutputPatternElement cr.(r_InTypes)) cr.(r_outpat) ).

Definition parse(ct: ConcreteTransformation) : Transformation :=
  buildTransformation 
    (max (map (length (A:=SourceModelClass)) (map r_InTypes (ConcreteTransformation_getConcreteRules ct))))
    (map parseRule (ConcreteTransformation_getConcreteRules ct)).

End Parser.

