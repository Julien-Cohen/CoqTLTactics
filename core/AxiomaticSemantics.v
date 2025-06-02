(** This module specifies the behavior of the model transformation engine in an axiomatic way.
    It is non-deterministic.

    We also show here that the operational semantics it correct with respect to this axiomatic semantics. *)

From core 
  Require
   utils.Utils 
   Model 
   Syntax 
   TransformationConfiguration 
   UserExpressions 
   TraceLink 
   Semantics.

Import 
  NotationUtils
  OptionListUtils
  Model 
  Syntax 
  TransformationConfiguration 
  UserExpressions 
  TraceLink.


Section Axiomatic.

Context {tc: TransformationConfiguration}.



(** * Pattern matching *)

Definition isTuple (sm : SourceModel) ip : Prop := 
  List.incl ip sm.(modelElements).


Lemma prop1 : forall tr sm ip,
  List.In ip (Semantics.allTuples tr sm) -> isTuple sm ip.
Proof.
  unfold Semantics.allTuples.
  unfold isTuple.

  intros ; eapply TupleUtils.tuples_up_to_n_incl ; eassumption.
Qed. 



Definition matchingRule (tr: Transformation) (sm : SourceModel) (sp: InputPiece) r : Prop :=
    List.In r tr.(rules) /\ UserExpressions.guard_ok r sm sp.


(** Correct and complete *)
Lemma prop2 :
 forall tr sm sp r,
   List.In r (Semantics.matchingRules tr sm sp) <-> matchingRule tr sm sp r.
Proof.
  unfold Semantics.matchingRules.
  unfold matchingRule.
  setoid_rewrite filter_In.
  unfold guard_ok.
  unfold evalGuard.
  tauto.
Qed.




(** * Building traces *)

Inductive traceElementOnPiece_rel (o: OutputPatternUnit) (sm: SourceModel) (sp: InputPiece) (iter: nat)
  : TraceLink -> Prop :=
    | r1 : 
      forall v, 
        evalOutputPatternUnit_rel o sm sp iter v ->
        traceElementOnPiece_rel o sm sp iter
         {| 
           source := (sp, iter, o.(opu_name)) ;
            produced := v ;
            linkPattern := o.(opu_link) 
          |}.


(** Correct and complete *)
Lemma prop3 : 
  forall o sm sp it tl,
  traceElementOnPiece_rel o sm sp it tl <-> Semantics.traceElementOnPiece o sm sp it = Some tl.
Proof.
  unfold Semantics.traceElementOnPiece.
  intros ; split.
  + intro H.
    inversion_clear H.
    unfold evalOutputPatternUnit_rel in H0.
    unfold evalOutputPatternUnit.
    rewrite H0.
    reflexivity.
  + intro H ; OptionUtils.monadInv H.
    constructor.
    exact H.
Qed.



Inductive traceIterationOnPiece_rel (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) (tl:TraceLink) : Prop :=
   | r2: forall o, 
        List.In o r.(r_outputPattern) ->
        traceElementOnPiece_rel o sm sp iter tl -> 
      traceIterationOnPiece_rel r sm sp iter tl.


(** Correct and complete *)
Lemma prop4 : forall r sm sp it tlk, 
  traceIterationOnPiece_rel r sm sp it tlk <-> List.In tlk (Semantics.traceIterationOnPiece r sm sp it).
Proof.
  unfold Semantics.traceIterationOnPiece.
  setoid_rewrite in_flat_map.
  setoid_rewrite in_optionToList.
  setoid_rewrite <- prop3.
  intros ; split ; intro H. 
  + inversion_clear H.
    eauto.
  + destruct H as (o & H1 & H2).
    econstructor ; eauto.
Qed.



Inductive traceRuleOnPiece_rel (r: Rule) (sm: SourceModel) (sp: InputPiece) (tlk:TraceLink) : Prop :=
  | r3 : 
    forall nb_it current_it, 
       current_it < nb_it -> 
       evalIterator_rel r sm sp nb_it ->
       traceIterationOnPiece_rel r sm sp current_it tlk ->
       traceRuleOnPiece_rel r sm sp tlk.


(* Correct and complete *)
Lemma prop5 : forall r sm sp tlk, 
  traceRuleOnPiece_rel r sm sp tlk <-> List.In tlk (Semantics.traceRuleOnPiece r sm sp).
Proof.
  unfold Semantics.traceRuleOnPiece.
  setoid_rewrite in_flat_map.
  setoid_rewrite <- prop4.
  intros ; split ; intro H.
  + inversion_clear H. 
    apply UserExpressions.p1 in H1.
    rewrite H1.
    exists current_it ; split ; [ | auto].
    apply in_seq.
    simpl.
    Lia.lia.
  + destruct H as (current_it & H1 & H2).
    econstructor ; [ | apply UserExpressions.c1 | exact H2].
    apply in_seq in H1.  
    simpl in H1.
    Lia.lia.
Qed.



Inductive traceTrOnPiece_rel (tr: Transformation) (sm : SourceModel) (sp: InputPiece) (tl: TraceLink) : Prop :=
  | r4 : forall r, 
    traceRuleOnPiece_rel r sm sp tl ->
    matchingRule tr sm sp r ->
      traceTrOnPiece_rel tr sm sp tl.


(** Correct and complete *)
Lemma prop6 : forall tr sm sp tlk,
  traceTrOnPiece_rel tr sm sp tlk <-> List.In tlk (Semantics.traceTrOnPiece tr sm sp).
Proof.
  unfold Semantics.traceTrOnPiece.
  setoid_rewrite in_flat_map.
  setoid_rewrite <- prop5.
  setoid_rewrite prop2.
  intros ; split ; intro H.
  + inversion_clear H. eauto.
  + destruct H as (r & H1 & H2).
    econstructor ; eauto.
Qed.



Inductive in_trace (tr: Transformation) (sm : SourceModel) (tl:TraceLink) : Prop :=
  | r5 : forall sp,
     traceTrOnPiece_rel tr sm sp tl ->
      isTuple sm sp ->
      List.length sp <= tr.(arity) -> (* to be coherent with the reference engine *)
    in_trace tr sm tl .  


(** Correct and complete *)
Lemma prop7 : forall tr sm tlk, 
  in_trace tr sm tlk <-> List.In tlk (Semantics.compute_trace tr sm).
Proof.
  unfold Semantics.compute_trace.
  setoid_rewrite in_flat_map.
  setoid_rewrite <- prop6.
  intros ; split ; intro H.
  + inversion_clear H.
    exists sp ; split ; [ | assumption].
    unfold Semantics.allTuples.
    apply TupleUtils.tuples_up_to_n_incl_length.
    unfold isTuple in H1.
    auto.
  + destruct H as (ip & H1 & H2).
    econstructor ; [ eassumption | | ].
    - eapply prop1 ; eassumption.
    - unfold Semantics.allTuples in H1.
      eapply TupleUtils.tuple_length ; eassumption.
Qed.



Definition is_trace trans sm tra : Prop :=
  forall lk, List.In lk tra <-> in_trace trans sm lk.    
(* We could also have used a set comprehension definition. *)


Lemma prop8 : forall trans sm, is_trace trans sm (Semantics.compute_trace trans sm).
Proof.
  unfold is_trace.
  setoid_rewrite prop7.
  tauto.
Qed.


(* Two traces (list) represent the same set. *)
Remark is_trace_incl_right : forall tr sm tra1 tra2,
  is_trace tr sm tra1 -> is_trace tr sm tra2 -> incl tra1 tra2.
Proof.
  unfold is_trace.
  intros.
  unfold incl.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.


Remark is_trace_incl_eq : forall tr sm tra1 tra2,
  is_trace tr sm tra1 -> is_trace tr sm tra2 -> (forall e, In e tra1 <-> In e tra2).
Proof.
  unfold is_trace.
  intros.
  setoid_rewrite H.
  setoid_rewrite H0.
  tauto.
Qed.




(** * Apply link part of the r.h.s of rules (uses traces) **)

Inductive apply_link_pattern_rel (tra:Trace) (sm:SourceModel) (tlk:TraceLink) (lk:TargetLinkType) : Prop := 
   | rr : 
    List.In lk (tlk.(linkPattern) (drop tra) (getIteration tlk) sm (getSourcePiece tlk) tlk.(produced)) ->
      apply_link_pattern_rel tra sm tlk lk. 
  
(* FIXME 
  In the axiomatic semantics, several traces are possible (the order of tracelinks in not enforced).

  For this reason, some relations are parameterized by a trace.

  For two different traces, [tlk.(linkPattern) (drop tra)] could give different results because the 
  user expressions are not limited in their use of the trace. 

  For this reason, we cannot get an equivalence between the axiomatic semantics and the operational semantics.
  Therefore, some results below deal with correctness and completeness 
  while other results only deal with correctness.

  Other possibilites to think about to get completeness:
    * Specify the order in traces in the axiomatic semantics.
    * Use sets instead of lists in traces.
    * Restrict the access of user to traces with accessor that do not take the order into account.

*) 



(** Correct and complete. *)
Lemma prop9 : forall tra sm tlk lk,
  List.In lk (Semantics.apply_link_pattern tra sm tlk) <->
  apply_link_pattern_rel tra sm tlk lk.
Proof.
  unfold Semantics.apply_link_pattern.
  intros.
  split ; intros.
  + econstructor.
    eassumption.
  + inversion_clear H. assumption.
Qed.



Inductive applyTrLkOnModel_rel tra (sm : SourceModel) (lk: TargetLinkType) : Prop :=
 | r6 : forall tlk,
 (*   is_trace tr sm tra ->*) (* FIXME What is the best level to enforce this ? *)
    List.In tlk tra -> 
    apply_link_pattern_rel tra sm tlk lk -> 
    applyTrLkOnModel_rel tra sm lk. 


(** Correctness & completeness. *)
Lemma prop10 : forall sm tra lk,
(*   is_trace tr sm tra -> *)
   List.In lk (Semantics.applyTrLkOnModel sm tra) <->
  applyTrLkOnModel_rel tra sm lk.
Proof.
  unfold Semantics.applyTrLkOnModel.
  setoid_rewrite in_flat_map.
  intros.
  split ; intros.
  + destruct H as (k & H1 & H2).
    econstructor ; eauto.
    eapply prop9 ; eassumption.
  + inversion_clear H.
    apply prop9 in H1.
    eauto. 
Qed.




(** * Execute **)

(** Main definition below. *)

Inductive is_produced_element (tr:Transformation) sm : TargetElementType -> Prop :=
    | r7 : forall a b c, 
        in_trace tr sm {| source := a; produced := b; linkPattern := c |} ->
        is_produced_element tr sm b.


(** Correctness & completeness *)
Lemma prop11 : forall tr sm e,
  In e ( (Semantics.execute tr sm).(modelElements)) <->
  is_produced_element tr sm e .
Proof.
  unfold Semantics.execute.
  simpl modelElements.
  unfold Semantics.produced_elements.
  intros.
  setoid_rewrite in_map_iff.
  split ; intro.
  + destruct H as (k & H1 & H2).  
    destruct k.
    simpl in H1.
    subst.
    econstructor. apply prop7. eassumption.
  + inversion_clear H.
    apply prop7 in H0.
    eexists ; split ; [ | exact H0] ; reflexivity.
Qed.


Inductive is_produced_link tra sm (lk:TargetLinkType): Prop :=
    | r8 : (*forall tra,*)  
        (*is_trace tr sm tra ->*)
        applyTrLkOnModel_rel tra sm lk->
        is_produced_link tra sm lk.


(** Correctness & completeness. *)
Lemma prop12 : forall tr sm lk,  
  In lk ( (Semantics.execute tr sm).(modelLinks)) <->
  is_produced_link (Semantics.compute_trace tr sm) sm lk .
Proof.
  unfold Semantics.execute.
  simpl modelLinks.
  intros.
  split; intro.
  + apply prop10  in H. 
    econstructor.
    assumption.
  + inversion_clear H.
    apply prop10.
    assumption.
Qed.

(* FIXME Warning : make the difference between: 
   1) The computed result is one possible result.
   2) The computed result is included in a possible result.
      Example: an empty model is always included in any correct result, 
      but we generally don't accept it as a correct result.
   3) The computed result is the union of several correct results.
      In particular, an engine should consider a given trace, not all the possible traces.
      Question: how would we consider a parallel version of an engine where each worker has 
      a different correct trace ?
*)


Definition is_result (tr:Transformation) (sm:SourceModel) (tm:TargetModel): Prop :=
  (forall e, (List.In e tm.(modelElements) <-> is_produced_element tr sm e)) /\ 
  (exists tra, is_trace tr sm tra /\ forall lk, (List.In lk tm.(modelLinks) <-> is_produced_link tra sm lk)).


(** Correctness *)
Lemma prop13 : forall tr sm,  is_result tr sm (Semantics.execute tr sm).
Proof.
  unfold is_result.
  split.
  + apply prop11.
  + exists (Semantics.compute_trace tr sm).
    split.
    - apply prop8.
    - apply prop12.
Qed.


End Axiomatic.

  
