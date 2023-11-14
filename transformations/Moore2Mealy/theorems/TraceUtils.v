Require Moore2Mealy.theorems.Elements.

Import List Model String.
Import NotationUtils Semantics.
Import PoorTraceLink.

Import Moore2Mealy.

(** Utilities on traces built by the Moore2Mealy transformation.
    In particular, all the results on [resolve], which appears in the code of the M2M transformation, rely on traces. *)

(** There are exactly two kinds of correspondences in traces (one for each rule) : *)
Lemma in_trace_inv (m:Moore.M) t :
In t (RichTraceLink.drop (traceTrOnModel Moore2Mealy m)) ->
   (exists a , 
       t = buildTraceLink 
             ([Moore.Transition a], 0, "t"%string)
             (Mealy.Transition (OptionUtils.valueOption (convert_transition m a) (dummy a))))
   \/ (exists s , 
          t = 
            buildTraceLink
              ([Moore.State s], 0, "s"%string)
              (Mealy.State (Moore2Mealy.convert_state s))).
Proof.
  intro H.
  Tactics.exploit_in_trace H ; [ right | left ] ;
  eexists ; reflexivity. 
Qed.

(** We can statically know what each State will yield in the trace: *)
Lemma state_in_trace (m:Moore.M) (s:Moore.State_t) : 
  In (Moore.State s) m.(modelElements) ->
  In (PoorTraceLink.buildTraceLink 
        ((Moore.State s) :: nil, 0, "s"%string) 
        (Mealy.State (Moore2Mealy.convert_state s))
    )
    (RichTraceLink.drop (Semantics.traceTrOnModel Moore2Mealy m)).
Proof.
  intro IN.
  unfold RichTraceLink.drop.
  apply in_map_iff.
  eexists.
  split.
  2:{
    Tactics.destruct_in_trace_G.
    exists (Moore.State s :: nil).
    split.
    { apply @Tactics.allModelElements_allTuples ; auto.  } 
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
      (RichTraceLink.drop (traceTrOnModel Moore2Mealy  m)).
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
  
  Tactics.exploit_in_trace IN1; 
  Tactics.exploit_in_trace IN2 ;
  PropUtils.inj EQ0 ;
  PropUtils.inj EQ ; auto.
  discriminate.
  discriminate.
Qed.


Lemma in_find m : 
  forall c,
    In (buildTraceLink
          ([Moore.State c], 0, "s"%string)
          (Mealy.State (Moore2Mealy.convert_state c))) 
      (RichTraceLink.drop (traceTrOnModel Moore2Mealy m)) ->

      find (source_compare ([Moore.State c], 0, "s"%string)) (RichTraceLink.drop (traceTrOnModel Moore2Mealy m)) = 
        Some 
          (buildTraceLink ([Moore.State c], 0, "s"%string) 
             (Mealy.State (Moore2Mealy.convert_state c))).
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

Lemma in_resolve m s : 
  In (buildTraceLink 
        ([Moore.State s], 0, "s"%string)
        (Mealy.State (Moore2Mealy.convert_state s))) (RichTraceLink.drop (traceTrOnModel Moore2Mealy m)) ->
  Resolve.resolveIter (RichTraceLink.drop (traceTrOnModel  Moore2Mealy m)) "s" [Moore.State s] 0 = 
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





Lemma in_Resolve_trace_2 s (m : Moore.M) :
  
  In (Moore.State s) m.(modelElements) -> 
  
  Resolve.resolve (RichTraceLink.drop (traceTrOnModel Moore2Mealy m)) "s" [Moore.State s]  =  
    Some (Mealy.State (Moore2Mealy.convert_state s)) 
  .
Proof.
  intro H.
  unfold Resolve.resolve.
  apply state_in_trace in H.
  rewrite in_resolve ; auto.
Qed.

