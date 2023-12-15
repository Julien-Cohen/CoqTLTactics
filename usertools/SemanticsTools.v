(** SemanticTools : Bi-directional results on the transformation engine defined in [Semantics]. *) 

Require Semantics.

Import String Bool utils.Utils Model Syntax TransformationConfiguration Semantics TraceLink.


#[global]
Hint Unfold 
  Semantics.traceTrOnPiece 
  Semantics.traceRuleOnPiece 
  Semantics.traceIterationOnPiece 
  Semantics.traceElementOnPiece 
  Semantics.produced_elements 
  : trace.

#[global]
Hint Unfold 
  Semantics.execute 
  Semantics.compute_trace 
  Semantics.produced_elements : semantics.



(** * On [allTuples] *) 

Lemma in_allTuples_incl {tc:TransformationConfiguration} tr sm :
  forall t, 
    In t (allTuples tr sm) <-> 
      (incl t (modelElements sm) /\ length t <= arity tr).
Proof.
  unfold allTuples.
  setoid_rewrite  <- TupleUtils.tuples_up_to_n_incl_length.
  tauto.
Qed.

Corollary in_allTuples_singleton {tc:TransformationConfiguration} tr sm :
  forall t, 
    In [t] (allTuples tr sm) <-> 
      (In t (modelElements sm) /\ 0 < arity tr).
Proof.
  setoid_rewrite in_allTuples_incl. setoid_rewrite <- incl_singleton. tauto.
Qed.

Lemma in_allTuples_pair {tc:TransformationConfiguration} :
      forall t m a b,
        (t.(Syntax.arity) >= 2 
         /\ In a (modelElements m)
         /\ In b (modelElements m)) <->
        In [a;b] (allTuples t m).
Proof.
  intros. setoid_rewrite in_allTuples_incl.
  split.
  - intros (?&?&?). split.
    + apply List.incl_cons ; auto.
      apply List.incl_cons ; auto.
      apply List.incl_nil_l.
    + auto with arith.
  - intros (?&L).
    simpl in L.
    repeat ListUtils.explicit_incl H.
    auto.
Qed.

(** * On trace *)

Lemma in_compute_trace_inv {tc : TransformationConfiguration} tr sm :
  forall s i n res l,
  In 
    {| source := (s, i, n); produced := res ; linkPattern := l |}
    (compute_trace tr sm) 
  <-> 
      incl s (modelElements sm) 
      /\ length s <= tr.(arity)
      /\ exists r : Rule,
        In r tr.(rules)
        /\ UserExpressions.evalGuard r sm s = true 
        /\ In i (seq 0 (UserExpressions.evalIterator r sm s))
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
    unfold UserExpressions.evalOutputPatternUnit.
    unfold opu_element.
    rewrite E.
    reflexivity.
Qed.    


(** * On [modelElements] *)

Lemma in_modelElements_inv {tc:TransformationConfiguration} tr sm :
  forall e, In e (execute tr sm).(modelElements) <-> 
              exists s i n lp, 
                In 
                  {| 
                    source := (s, i, n);
                    produced := e ;
                    linkPattern := lp 
                  |} 
                  (compute_trace tr sm).
Proof.
  setoid_rewrite in_map_iff.
  intro ; split.
  + intros ([((?& ?) & ?) ? ?] &?&?).
    subst.
    repeat first [eexists | split | eassumption].
  + intros (?&?&?&?&?).
    repeat first [eexists | split | eassumption].
    reflexivity.
Qed.


(** * On [modelLinks] *)

Lemma in_modelLinks_inv {tc:TransformationConfiguration} tr sm :
  forall l, In l (execute tr sm).(modelLinks) <-> 
              exists s i n res lp,
                In 
                  {| 
                    source := (s, i, n);
                    produced := res ;
                    linkPattern := lp 
                  |} 
                  (compute_trace tr sm) 
                /\ In 
                     l 
                     (apply_link_pattern 
                        (compute_trace tr sm) 
                        sm 
                        {| 
                          source := (s, i, n);
                          produced := res ;
                          linkPattern := lp
                        |}).
Proof.
  setoid_rewrite in_flat_map at 1.
  intro ; split.
  + intros ([((?& ?) & ?) ? ?] &?&?). 
    repeat first [eexists | split | eassumption].
  + intros (?&?&?&?&?&?&?).
    repeat first [eexists | split | eassumption].
Qed.
