Require 
  Moore2Mealy.theorems.Elements.

Import 
  List Model String NotationUtils Semantics PoorTraceLink Moore2Mealy  NotationUtils Semantics.

Open Scope string_scope.

(** Utilities on traces built by the Moore2Mealy transformation.
    In particular, all the results on [resolve], which appears in the code of the M2M transformation, rely on traces. *)


(** We can statically know what each State will yield in the trace: *)
Lemma state_in_trace (m:Moore.M) (s:Moore.State_t) : 
  In (Moore.State s) m.(modelElements) ->
  In {| 
       source := ((Moore.State s) :: nil, 0, "s")  ;
       produced := (Mealy.State (Moore2Mealy.convert_state s))
    |}
    (TraceLink.drop (Semantics.compute_trace Moore2Mealy m)).
Proof.
  intro IN1.
  apply TraceLink.in_drop_inv.
  eexists.
  simpl. 
  TacticsFW.in_compute_trace_inv_singleton_fw "state" "s" IN1 ; reflexivity.
Qed.


(** Discrminating predicate to switch between [List.In] and [List.find]. 
We need to deal with List.find because it is used in the definition of Resolve.
*)

Lemma discr m:
  forall s : list Moore.Element * nat * string,
    ListUtils.discriminating_predicate
      (fun x : TraceLink => source_compare s x = true)
      (TraceLink.drop (compute_trace Moore2Mealy  m)).
Proof.
  intro s.
  intros a b IN1 IN2 C1 C2.
  destruct a.
  apply source_compare_correct in C1.
  simpl in C1.
  subst.
  destruct b.
  apply source_compare_correct in C2.
  simpl in C2.
  subst.
  f_equal.
  
  TacticsBW.exploit_in_trace IN1 ; 
  TacticsBW.exploit_in_trace IN2 ; auto. 

  PropUtils.unif EQ EQ0 ; reflexivity.
Qed.


Lemma in_find m : 
  forall c,
    In {|
         source := ([Moore.State c], 0, "s") ;
         produced := Mealy.State (Moore2Mealy.convert_state c)
      |} 
      (TraceLink.drop (compute_trace Moore2Mealy m)) ->

      find (source_compare ([Moore.State c], 0, "s")) (TraceLink.drop (compute_trace Moore2Mealy m)) = 
        Some 
          {|
            source := ([Moore.State c], 0, "s") ;
            produced := Mealy.State (Moore2Mealy.convert_state c)
          |}.
Proof.
  intros c H.
  apply ListUtils.in_find.
  { apply discr. }
  {
    unfold source_compare ; simpl.
    unfold TransformationConfiguration.SourceElement_eqb.
    simpl.    
    rewrite Metamodel.beq_refl ; reflexivity.
  }
  { exact H. }
Qed.            


(** Resolve is a lookup in the trace. Resolve is called from the user defined transformation. *)

Local Lemma in_trace_resolve m s : 
  In {| 
       source := ([Moore.State s], 0, "s") ;
       produced := Mealy.State (Moore2Mealy.convert_state s)
    |} 
    (TraceLink.drop (compute_trace Moore2Mealy m)) ->
  Resolve.resolveIter (TraceLink.drop (compute_trace  Moore2Mealy m)) "s" [Moore.State s] 0 = 
    Some (Mealy.State (Moore2Mealy.convert_state s)).
Proof.
  unfold Resolve.resolveIter. 
  intros IN1.
  specialize (in_find _ s IN1) ; intro T5 ; clear IN1.
  unfold TransformationConfiguration.SourceElementType ; simpl.
  rewrite T5.
  simpl produced.
  reflexivity.
Qed.


Lemma in_model_resolve s (m : Moore.M) :
  In (Moore.State s) m.(modelElements) -> 
  Resolve.resolve (TraceLink.drop (compute_trace Moore2Mealy m)) "s" [Moore.State s]  =  
    Some (Mealy.State (Moore2Mealy.convert_state s)).
Proof.
  intro H.
  unfold Resolve.resolve.
  apply state_in_trace in H.
  rewrite in_trace_resolve ; auto.
Qed.

