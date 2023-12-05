Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import TransformationConfiguration.
Require Import UserExpressions.

Require Import RichTraceLink.


Section Semantics.

Context {tc: TransformationConfiguration}.

(** * Pattern matching *)

Definition allTuples (tr: Transformation) (sm : SourceModel) : list InputPiece :=
  tuples_up_to_n sm.(modelElements) tr.(arity).

Lemma in_allTuples_incl tr sm :
  forall t, 
    In t (allTuples tr sm) <-> 
      (incl t (modelElements sm) /\ length t <= arity tr).
Proof.
  unfold allTuples.
  setoid_rewrite  <- tuples_up_to_n_incl_length.
  tauto.
Qed.

Corollary in_allTuples_incl_singleton tr sm :
  forall t, 
    In [t] (allTuples tr sm) <-> 
      (In t (modelElements sm) /\ 0 < arity tr).
Proof.
  setoid_rewrite in_allTuples_incl. setoid_rewrite <- incl_singleton. tauto.
Qed.

Definition matchingRules (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list Rule :=
  filter (fun (r:Rule) => evalGuard r sm sp) tr.(rules).



(** * Building traces *)

Definition traceElementOnPiece (o: OutputPatternUnit) (sm: SourceModel) (sp: InputPiece) (iter: nat)
  : option TraceLink :=
  match (evalOutputPatternUnit o sm sp iter) with
  | Some e => Some 
                {| source := (sp, iter, o.(opu_name)) ;
                  produced :=  e ;
                  linkPattern := o.(opu_link) |}
  | None => None
  end.

Definition traceIterationOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) :  Trace :=
  flat_map (fun o => optionToList (traceElementOnPiece o sm sp iter))
    r.(r_outputPattern).

Definition traceRuleOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) : Trace :=
  flat_map (traceIterationOnPiece r sm sp)
    (seq 0 (evalIterator r sm sp)).

Definition traceTrOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : Trace :=
  flat_map (fun r => traceRuleOnPiece r sm sp) (matchingRules tr sm sp).



Definition compute_trace (tr: Transformation) (sm : SourceModel) :  RichTraceLink.Trace :=
  flat_map (traceTrOnPiece tr sm) (allTuples tr sm).  

Lemma in_compute_trace_inv tr sm :
  forall a, 
  In a (compute_trace tr sm) <-> 
    exists p : InputPiece,
      
      incl p (modelElements sm) 
      /\ length p <= tr.(arity)
      /\ exists r : Rule,
        In r tr.(rules)
        /\ evalGuard r sm p = true 
        /\ exists i : nat,
          In i (seq 0 (evalIterator r sm p))
          /\ exists opu : OutputPatternUnit,
            In opu r.(r_outputPattern) 
            /\ exists e : TargetElementType,
              {|
                source := (p, i, opu.(opu_name));
                produced := e;
                linkPattern := opu.(opu_link)
              |} = a 
              /\ evalOutputPatternUnit opu sm p i = Some e.
Proof.
  repeat setoid_rewrite in_flat_map. 
  setoid_rewrite  optionToList_map.
  setoid_rewrite in_map_iff.
  setoid_rewrite  in_optionToList.
  setoid_rewrite filter_In.
  setoid_rewrite in_allTuples_incl.
  intro a ; split. 
  + intros (? & (( ? & ? ) & ? & ( ? & ? ) & ? & ? & ? & ? & ? & ? & ?)). 
    subst ; repeat (first [eexists | split]) ; eassumption. 
  + intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
    subst ; repeat (first [eexists | split]) ; eassumption. 
Qed.

Corollary in_compute_trace_inv_alt tr sm :
  forall a, 
  In a (compute_trace tr sm) <-> 
      incl (getSourcePiece a) (modelElements sm) 
      /\ length (getSourcePiece a) <= tr.(arity)
      /\ exists r : Rule,
        In r tr.(rules)
        /\ evalGuard r sm (getSourcePiece a) = true 
        /\ 
          In (getIteration a) (seq 0 (evalIterator r sm (getSourcePiece a)))
          /\ exists opu : OutputPatternUnit,
            In opu r.(r_outputPattern) 
            /\ getName a = opu.(opu_name) 
            /\ a.(linkPattern) = opu.(opu_link)
            /\ evalOutputPatternUnit opu sm (getSourcePiece a) (getIteration a) = Some a.(produced).
Proof.
  repeat setoid_rewrite in_compute_trace_inv. 
  intro a.
  split.
  + intros (?&?&?&?&?&?&?&?&?&?&?&?&?).
    subst a.
    repeat first [eexists | split] ; eauto.
  + intros (?&?&?&?&?&?&?&?&?&?&?).
    destruct a.
    destruct source as ((?&?)&?).
    simpl in H5. 
    simpl in *.
    repeat first [eexists | split | f_equal] ; eauto.
Qed.

Corollary in_compute_trace_inv_alt_alt tr sm :
  forall s i n res l,
  In 
    {| source := (s, i, n); produced := res ; linkPattern := l |}
    (compute_trace tr sm) 
  <-> 
      incl s (modelElements sm) 
      /\ length s <= tr.(arity)
      /\ exists r : Rule,
        In r tr.(rules)
        /\ evalGuard r sm s = true 
        /\ In i (seq 0 (evalIterator r sm s))
          /\ exists opu : OutputPatternUnit,
            In opu r.(r_outputPattern) 
            /\ n = opu.(opu_name) 
            /\ l = opu.(opu_link)
            /\ evalOutputPatternUnit opu sm s i = Some res.
Proof.
  intros.
  setoid_rewrite in_compute_trace_inv_alt ; simpl.
  split.
  + intros (?&?&?&?&?&?&?&?&?&?&?).
    repeat first [eexists | split] ; eauto.
  + intros (?&?&?&?&?&?&?&?&?&?&?).
    repeat first [eexists | split | f_equal] ; eauto.
Qed.

Corollary in_compute_trace_inv_alt_alt_alt tr sm :
  forall s i n res l,
  In 
    {| source := (s, i, n); produced := res ; linkPattern := l |}
    (compute_trace tr sm) 
  <-> 
      incl s (modelElements sm) 
      /\ length s <= tr.(arity)
      /\ exists r : Rule,
        In r tr.(rules)
        /\ evalGuard r sm s = true 
        /\ In i (seq 0 (evalIterator r sm s))
        /\ exists opu_el,
           In {| opu_name := n ; opu_element := opu_el ; opu_link := l |} r.(r_outputPattern) 
            /\  opu_el i sm s = Some res.
Proof.
  intros.
  setoid_rewrite in_compute_trace_inv_alt_alt ; simpl.
  split.
  + intros (?&?&?&?&?&?&z&?&?&?&?).
    destruct z.
    subst. simpl.
    repeat (split ; auto).
    exists x.
    repeat (split ; auto).
    exists opu_element.
    split ; auto.
  + intros (?&?&?&?&?&?&?&?&?).
    repeat first [eexists | split | f_equal] ; eauto.
Qed.

(** * Apply link part of the r.h.s of rules (uses traces) **)

Definition apply_link_pattern tls sm lk := 
    lk.(linkPattern) (drop tls) (getIteration lk) sm (getSourcePiece lk) lk.(produced).
  

Definition applyTrOnModel (sm : SourceModel) (tls:Trace): list TargetLinkType :=
    flat_map (apply_link_pattern tls sm) tls. 




(** * Execute **)

Definition produced_elements := map RichTraceLink.produced.

Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  let t := compute_trace tr sm
  in
  {|
    modelElements := produced_elements t ;
    modelLinks := applyTrOnModel sm t
  |}.


Lemma in_modelElements_inv tr sm :
  forall e, In e (execute tr sm).(modelElements) <-> 
              exists a : TraceLink, 
                produced a = e 
                /\ In a (compute_trace tr sm).
Proof.
  setoid_rewrite in_map_iff.
  tauto.
Qed.

Lemma in_modelLinks_inv tr sm :
  forall l, In l (execute tr sm).(modelLinks) <-> 
              exists a : TraceLink,
                In a (compute_trace tr sm) 
                /\ In l (apply_link_pattern (compute_trace tr sm) sm a).
Proof.
  setoid_rewrite in_flat_map at 1.
  tauto.
Qed.

End Semantics.

  
