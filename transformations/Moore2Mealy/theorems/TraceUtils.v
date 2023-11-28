Require Moore2Mealy.theorems.Elements.

Import List Model String.
Import NotationUtils Semantics.
Import PoorTraceLink.

Import Moore2Mealy.

(** Utilities on traces built by the Moore2Mealy transformation.
    In particular, all the results on [resolve], which appears in the code of the M2M transformation, rely on traces. *)



(** We can statically know what each State will yield in the trace: *)
Lemma state_in_trace (m:Moore.M) (s:Moore.State_t) : 
  In (Moore.State s) m.(modelElements) ->
  In {| 
       source := ((Moore.State s) :: nil, 0, "s"%string)  ;
       produced := (Mealy.State (Moore2Mealy.convert_state s))
    |}
    (RichTraceLink.drop (Semantics.compute_trace Moore2Mealy m)).
Proof.
  intro IN.
  unfold RichTraceLink.drop.
  apply in_map_iff.
  eexists.
  split.
  2:{
    apply TacticsFW.in_trace_split.
    exists (Moore.State s :: nil).
    repeat split.
    { apply ListUtils.incl_singleton. assumption. }
    { compute. auto. }
    { compute. left. reflexivity. }
  }
  {  reflexivity. }
Qed.


(** Discrminating predicate to switch between [List.In] and [List.find]. 

We need to deal with List.find because it is used in the definition of Resolve.
*)

Import NotationUtils.
Import Semantics.


Lemma discr m:
  forall s : list Moore.Element * nat * string,
    ListUtils.discriminating_predicate
      (fun x : TraceLink => source_compare s x = true)
      (RichTraceLink.drop (compute_trace Moore2Mealy  m)).
Proof.
  intro s.
  intros a b IN1 IN2 C1 C2.
  destruct a.
  apply source_compare_correct in C1.
  simpl in C1.
  subst.
  2:{
    simpl. apply Moore.internal_Element_dec_bl.
  }    
  destruct b.
  apply source_compare_correct in C2.
  simpl in C2.
  subst.
  2:{
    apply Moore.internal_Element_dec_bl.
  }    
  f_equal.
  
  TacticsBW.exploit_in_trace IN1; 
  TacticsBW.exploit_in_trace IN2 ; auto. 

  PropUtils.unif EQ0 EQ1 ; reflexivity.
Qed.


Lemma in_find m : 
  forall c,
    In {|
         source := ([Moore.State c], 0, "s"%string) ;
         produced := Mealy.State (Moore2Mealy.convert_state c)
      |} 
      (RichTraceLink.drop (compute_trace Moore2Mealy m)) ->

      find (source_compare ([Moore.State c], 0, "s"%string)) (RichTraceLink.drop (compute_trace Moore2Mealy m)) = 
        Some 
          {|
            source := ([Moore.State c], 0, "s"%string) ;
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
    rewrite Moore.internal_State_t_dec_lb ; reflexivity.
  }

  { exact H. }

Qed.            


(* Resolve is a lookup in the trace. Resolve is called from the user defined transformation. *)

Local Lemma in_trace_resolve m s : 
  In {| 
       source := ([Moore.State s], 0, "s"%string) ;
       produced := Mealy.State (Moore2Mealy.convert_state s)
    |} 
    (RichTraceLink.drop (compute_trace Moore2Mealy m)) ->
  Resolve.resolveIter (RichTraceLink.drop (compute_trace  Moore2Mealy m)) "s" [Moore.State s] 0 = 
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
  
  Resolve.resolve (RichTraceLink.drop (compute_trace Moore2Mealy m)) "s" [Moore.State s]  =  
    Some (Mealy.State (Moore2Mealy.convert_state s)) 
  .
Proof.
  intro H.
  unfold Resolve.resolve.
  apply state_in_trace in H.
  rewrite in_trace_resolve ; auto.
Qed.

