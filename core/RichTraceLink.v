Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.

Require Syntax.

(** * Syntax

      In this section, we introduce _one possible_ abstract syntax of the CoqTL transformation engine.  
      ---- *)

Section TraceLink.

Context {tc: TransformationConfiguration}.

(** ** Traces 

        We introduce the concept of trace in the syntax to track relationship of a produced element (target) and 
        the source pattern that generates it.   *)

Record TraceLink : Type :=
  buildTraceLink  
    { 
      source : InputPiece * nat * string ;
      produced : TargetElementType ;
      linkPattern : PoorTraceLink.Trace -> nat -> SourceModel -> InputPiece -> TargetElementType -> list TargetLinkType
    }.

Definition getSourcePiece (tl: TraceLink):=
  match tl.(source) with 
    (sp, i, n)  => sp
  end.

Definition getIteration (tl: TraceLink):=
  match tl.(source) with 
    (sp, i, n)  => i
  end.

Definition getName (tl: TraceLink):=
  match tl.(source) with 
     (sp, i, n) => n
  end.

Open Scope bool_scope.


Definition source_compare (s:InputPiece * nat * string) (t:TraceLink) : bool :=
  match s with 
    (e,i,n) =>
      list_beq tc.(SourceElement_eqb) (getSourcePiece t) e
      && Nat.eqb (getIteration t) i
      && String.eqb (getName t) n
  end.



Lemma source_compare_refl : 
  (forall a,  SourceElement_eqb a a = true) ->
  forall a b c, 
    source_compare a {| source := a ; produced := b ; linkPattern := c |} = true.
Proof.
  intros R a b c.
  destruct a as ((l & i) & n). 
  simpl.
  unfold getSourcePiece, getIteration, getName ; simpl.
  rewrite list_beq_refl ; [ | exact R].
  rewrite NPeano.Nat.eqb_refl.
  rewrite String.eqb_refl. 
  reflexivity.
Qed.

(* Not Used *)
(* The requirement is too strong for the general case *)
Lemma source_compare_correct :
  (forall a b : Metamodel.ElementType SourceMetamodel,
  Metamodel.elements_eqdec SourceMetamodel a b = true -> a = b) ->
  forall a b,
    source_compare a b = true -> b.(source) = a.
Proof.
  intro H1.
  unfold source_compare.
  intros a b H2 ; destruct a ; destruct p ; destruct b.
  simpl. destruct source0 ; simpl in *.
  BoolUtils.destruct_conjunctions.
  destruct p ; simpl in *.
  apply EqNat.beq_nat_true in H2 ; subst .
  apply String.eqb_eq in H0 ; subst.
  apply list_beq_correct in H ; subst.
  + reflexivity.
  + exact H1. 
Qed.

Definition convert (a:TraceLink) : PoorTraceLink.TraceLink :=
  PoorTraceLink.buildTraceLink a.(source) a.(produced).

Definition drop := map convert.

End TraceLink.

Arguments TraceLink {_}.

Arguments source_compare : simpl never.

Notation Trace := (list TraceLink).

