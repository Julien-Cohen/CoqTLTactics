Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import TransformationConfiguration.

(** Transformation rules are defined by the user. They are made of expressions (patterns/guards, number of iterations, output elements, output links) which are here encoded by Gallina/Coq functions (higher-order abstract syntax, see the module [Syntax]). 

In this module we deal with application of those functions (or instantiation of user expressions). *)

Section Expressions.

Context {tc: TransformationConfiguration}.



Definition evalGuard (r : Rule) (sm: SourceModel) (sp: InputPiece) : bool :=
  r.(r_guard) sm sp.

Inductive guard_ok r sm sp : Prop :=
  | OK : r.(r_guard) sm sp = true -> guard_ok r sm sp.

Definition evalIterator (r : Rule) (sm: SourceModel) (sp: InputPiece) :
  nat :=
  match r.(r_iterator) sm sp with
  | Some n => n
  | _ => 0
  end.

Inductive evalIterator_rel r sm sp : nat -> Prop :=
  | it_some : forall n, r.(r_iterator) sm sp = Some n -> evalIterator_rel r sm sp n
  | it_none : r.(r_iterator) sm sp = None -> evalIterator_rel r sm sp 0.

Definition evalOutputPatternUnit (o: OutputPatternUnit) (sm: SourceModel) (sp: InputPiece) (iter: nat) 
  : option TargetElementType := 
  o.(opu_element) iter sm sp.

Inductive evalOutputPatternUnit_rel o sm sp it e :=
  | ev_out_el : o.(opu_element) it sm sp = Some e -> evalOutputPatternUnit_rel o sm sp it e.

Definition evalOutputPatternLink
            (sm: SourceModel) (sp: InputPiece) (oe: TargetElementType) (iter: nat) (tra: list TraceLink)
            (o: OutputPatternUnit)
  : list TargetLinkType :=
  o.(opu_link) tra iter sm sp oe.

Inductive evalOutputPatternLink_rel sm sp oe it tra o l :=
  | ev_out_lk : List.In l (o.(opu_link) tra it sm sp oe) -> 
  evalOutputPatternLink_rel sm sp oe it tra o l.


End Expressions.
