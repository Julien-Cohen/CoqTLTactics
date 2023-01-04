Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.

(** * Syntax

      In this section, we introduce _one possible_ abstract syntax of the CoqTL transformation engine.  
      ---- *)

Section TraceLink.

Context {tc: TransformationConfiguration}.

(** ** Traces 

        We introduce the concept of trace in the syntax to track relationship of a target element and 
        the source pattern that generates it   *)

Record TraceLink : Type :=
  buildTraceLink  
    { 
      source : (list SourceElementType) * nat * string ;
      target : TargetElementType 
    }.

Definition TraceLink_getSourcePattern (tl: TraceLink):=
  match tl.(source) with 
    (sp, i, n)  => sp
  end.

Definition TraceLink_getIteration (tl: TraceLink):=
  match tl.(source) with 
    (sp, i, n)  => i
  end.

Definition TraceLink_getName (tl: TraceLink):=
  match tl.(source) with 
     (sp, i, n) => n
  end.

Open Scope bool_scope.


Definition source_compare (s:(list SourceElementType) * nat * string) (t:TraceLink) : bool :=
  match s with 
    (e,i,n) =>
      list_beq tc.(SourceElement_eqb) (TraceLink_getSourcePattern t) e
      && Nat.eqb (TraceLink_getIteration t) i
      && String.eqb (TraceLink_getName t) n
  end.



Lemma source_compare_refl : 
  (forall a,  SourceElement_eqb a a = true) ->
  forall a b, 
    source_compare a {| source := a ; target := b |} = true.
Proof.
  intro R.    
  intros a b.
  destruct a. destruct p.
  unfold source_compare.
  unfold TraceLink_getSourcePattern ; simpl.
  unfold TraceLink_getIteration ; simpl.
  unfold TraceLink_getName ; simpl.
  rewrite list_beq_refl ; [ | exact R].
  rewrite NPeano.Nat.eqb_refl.
  rewrite String.eqb_refl. 
  reflexivity.
Qed.

End TraceLink.

Arguments TraceLink {_}.

Arguments source_compare : simpl never.
