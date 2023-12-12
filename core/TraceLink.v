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


Definition convert (a:TraceLink) : PoorTraceLink.TraceLink :=
  {| 
    PoorTraceLink.source := a.(source) ;
    PoorTraceLink.produced := a.(produced)
  |}.

Definition drop := map convert.

Lemma in_drop_inv t:
  forall a, In a (drop t) <-> exists x , In {| source := a.(PoorTraceLink.source) ; produced := a.(PoorTraceLink.produced) ; linkPattern := x |} t.
Proof.
  setoid_rewrite in_map_iff.
  unfold convert.
  intro ; split.
  + intros (x&?&?) ; destruct x ; subst ; simpl ; eexists ; eassumption.
  + destruct a ; simpl.
    intros (?&?) ; eexists ; split ; [ | eassumption] ; reflexivity. 
Qed.

End TraceLink.

Arguments TraceLink {_}.

Notation Trace := (list TraceLink).

Ltac lift H := 
  match type of H with
  | In _ (TraceLink.drop _) => 
      apply in_drop_inv in H ; 
      destruct H as (? & H)  
  end.


#[global]
Hint Unfold 
  getSourcePiece
  linkPattern
  getIteration
  getName
  produced
  source : tracelink.
