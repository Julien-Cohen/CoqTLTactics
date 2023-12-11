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

Lemma in_allTuples_2 :
      forall t m a b,
        t.(Syntax.arity) >= 2 ->
        In a (modelElements m) ->
        In b (modelElements m) ->
        In [a;b] (allTuples t m).
Proof.
  intros until t ; intros HA IN1 IN2.
  setoid_rewrite in_allTuples_incl ; split.
  {
    apply List.incl_cons ; auto.
    apply List.incl_cons ; auto.
    apply List.incl_nil_l.
  }
  {
    simpl.
    auto with arith.
  }
Qed.

Definition matchingRules (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list Rule :=
  filter (fun (r:Rule) => evalGuard r sm sp) tr.(rules).



(** * Building traces *)

Definition traceElementOnPiece (o: OutputPatternUnit) (sm: SourceModel) (sp: InputPiece) (iter: nat)
  : option TraceLink :=
    v <- evalOutputPatternUnit o sm sp iter ;
    return {| 
        source := (sp, iter, o.(opu_name)) ;
        produced := v ;
        linkPattern := o.(opu_link) 
      |}.

Definition traceIterationOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) :  Trace :=
  flat_map
    (fun o => optionToList (traceElementOnPiece o sm sp iter))
    r.(r_outputPattern).

Definition traceRuleOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) : Trace :=
  flat_map 
    (traceIterationOnPiece r sm sp)
    (seq 0 (evalIterator r sm sp)).

Definition traceTrOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : Trace :=
  flat_map 
    (fun r => traceRuleOnPiece r sm sp) 
    (matchingRules tr sm sp).

Definition compute_trace (tr: Transformation) (sm : SourceModel) :  RichTraceLink.Trace :=
  flat_map 
    (traceTrOnPiece tr sm) 
    (allTuples tr sm).  

Lemma in_compute_trace_inv tr sm :
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
  setoid_rewrite in_flat_map. (* compute_trace *)
  setoid_rewrite in_flat_map. (* traceTrOnPiece *) 
  setoid_rewrite in_flat_map. (* traceRuleOnPiece *)
  setoid_rewrite in_flat_map. (* traceIterationOnPiece *)
  setoid_rewrite filter_In.   (* matchingRules *)
  setoid_rewrite  in_optionToList.
  unfold traceElementOnPiece.

  setoid_rewrite in_allTuples_incl.


  split.
  +  intros (?&(?&?)&?&(?&?)&?&?& [? e ?] &?& T).
     monadInv T.
     repeat first [split | eexists | eassumption].

  + intros (?&?&?&?&?&?&?&?& E).
    eexists.
    split. split ; eassumption .
    eexists.
    split. split ; eassumption.
    eexists. split ; [ eassumption | ].
    eexists. split ; [ eassumption| ].
    unfold evalOutputPatternUnit.
    unfold opu_element.
    rewrite E.
    reflexivity.
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




End Semantics.

  
