(** This module defines the behavior of the model transformation engine. *)

From core 
  Require
   utils.Utils 
   Model 
   Syntax 
   TransformationConfiguration 
   UserExpressions 
   TraceLink.

Import 
  NotationUtils
  OptionListUtils
  Model 
  Syntax 
  TransformationConfiguration 
  UserExpressions 
  TraceLink.


Section Semantics.

Context {tc: TransformationConfiguration}.

(** * Pattern matching *)

(* executable *)
Definition allTuples (tr: Transformation) (sm : SourceModel) : list InputPiece :=
  TupleUtils.tuples_up_to_n sm.(modelElements) tr.(arity).

(* predicative *)
Definition isTuple (sm : SourceModel) ip : Prop := 
  List.incl ip sm.(modelElements).

Lemma p1 : forall tr sm ip,
  List.In ip (allTuples tr sm) -> isTuple sm ip.
Proof.
  unfold allTuples.
  unfold isTuple.

  intros ; eapply TupleUtils.tuples_up_to_n_incl ; eassumption.
Qed. 


(* executable *)
Definition matchingRules (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list Rule :=
  List.filter (fun (r:Rule) => evalGuard r sm sp) tr.(rules).

(* predicative *)
Definition matchingRule (tr: Transformation) (sm : SourceModel) (sp: InputPiece) r : Prop :=
    List.In r tr.(rules) /\ UserExpressions.guard_ok r sm sp.

Lemma p2 :
 forall tr sm sp r,
   List.In r (matchingRules tr sm sp) <-> matchingRule tr sm sp r.
Proof.
  unfold matchingRules.
  unfold matchingRule.
  Search (In _ (filter _ _)).
  setoid_rewrite filter_In.
  unfold guard_ok.
  unfold evalGuard.
  tauto.
Qed.


(** * Building traces *)

(* executable *)
Definition traceElementOnPiece (o: OutputPatternUnit) (sm: SourceModel) (sp: InputPiece) (iter: nat)
  : option TraceLink :=
    v <- evalOutputPatternUnit o sm sp iter ;
    return {| 
        source := (sp, iter, o.(opu_name)) ;
        produced := v ;
        linkPattern := o.(opu_link) 
      |}.

(* predicatif *)
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

Lemma p3 : 
  forall o sm sp it tl,
  traceElementOnPiece_rel o sm sp it tl <-> traceElementOnPiece o sm sp it = Some tl.
Proof.
  unfold traceElementOnPiece.
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

(* executable *)
Definition traceIterationOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) :  Trace :=
  flat_map
    (fun o => optionToList (traceElementOnPiece o sm sp iter))
    r.(r_outputPattern).

(* predicatif *)
Inductive traceIterationOnPiece_rel (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) (tl:TraceLink) : Prop :=
   | r2: forall o, 
        List.In o r.(r_outputPattern) ->
        traceElementOnPiece_rel o sm sp iter tl -> 
      traceIterationOnPiece_rel r sm sp iter tl.

Lemma p4 : forall r sm sp it tlk, 
  traceIterationOnPiece_rel r sm sp it tlk <-> List.In tlk (traceIterationOnPiece r sm sp it).
Proof.
  unfold traceIterationOnPiece.
  Search (In _ (flat_map _ _)).
  setoid_rewrite in_flat_map.
  Search (In _ (optionToList _)).
  setoid_rewrite in_optionToList.
  setoid_rewrite <- p3.
  intros ; split ; intro H. 
  + inversion_clear H.
    eauto.
  + destruct H as (o & H1 & H2).
    econstructor ; eauto.
Qed.


(* executable *)
Definition traceRuleOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) : Trace :=
  flat_map 
    (traceIterationOnPiece r sm sp)
    (seq 0 (evalIterator r sm sp)).

(* predicatif *)
Inductive traceRuleOnPiece_rel (r: Rule) (sm: SourceModel) (sp: InputPiece) (tlk:TraceLink) : Prop :=
  | r3 : 
    forall nb_it current_it, 
       current_it < nb_it -> 
       evalIterator_rel r sm sp nb_it ->
       traceIterationOnPiece_rel r sm sp current_it tlk ->
       traceRuleOnPiece_rel r sm sp tlk.

Lemma p5 : forall r sm sp tlk, 
  traceRuleOnPiece_rel r sm sp tlk <-> List.In tlk (traceRuleOnPiece r sm sp).
Proof.
  unfold traceRuleOnPiece.
  setoid_rewrite in_flat_map.
  setoid_rewrite <- p4.
  intros ; split ; intro H.
  + inversion_clear H. 
    apply UserExpressions.p1 in H1.
    rewrite H1.
    exists current_it ; split ; [ | auto].
    Search (In _ (seq _ _)).
    apply in_seq.
    simpl.
    Lia.lia.
  + destruct H as (current_it & H1 & H2).
    econstructor ; [ | apply UserExpressions.c1 | exact H2].
    apply in_seq in H1.  
    simpl in H1.
    Lia.lia.
Qed.

(* executable *)
Definition traceTrOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : Trace :=
  flat_map 
    (fun r => traceRuleOnPiece r sm sp) 
    (matchingRules tr sm sp).

(* predicatif *)
Inductive traceTrOnPiece_rel (tr: Transformation) (sm : SourceModel) (sp: InputPiece) (tl: TraceLink) : Prop :=
  | r4 : forall r, 
    traceRuleOnPiece_rel r sm sp tl ->
    matchingRule tr sm sp r ->
      traceTrOnPiece_rel tr sm sp tl.

Lemma p6 : forall tr sm sp tlk,
  traceTrOnPiece_rel tr sm sp tlk <-> List.In tlk (traceTrOnPiece tr sm sp).
Proof.
  unfold traceTrOnPiece.
  setoid_rewrite in_flat_map.
  setoid_rewrite <- p5.
  setoid_rewrite p2.
  intros ; split ; intro H.
  + inversion_clear H. eauto.
  + destruct H as (r & H1 & H2).
    econstructor ; eauto.
Qed.


(* executable *)
Definition compute_trace (tr: Transformation) (sm : SourceModel) :  TraceLink.Trace :=
  flat_map 
    (traceTrOnPiece tr sm) 
    (allTuples tr sm).  

(* predicatif *)
Inductive in_trace (tr: Transformation) (sm : SourceModel) (tl:TraceLink) : Prop :=
  | r5 : forall sp,
     traceTrOnPiece_rel tr sm sp tl ->
      isTuple sm sp ->
      List.length sp <= tr.(arity) -> (* cohérence avec le moteur de référence *)
    in_trace tr sm tl .  

Lemma p7 : forall tr sm tlk, 
  in_trace tr sm tlk <-> List.In tlk (compute_trace tr sm).
Proof.
  unfold compute_trace.
  setoid_rewrite in_flat_map.
  setoid_rewrite <- p6.
  intros ; split ; intro H.
  + inversion_clear H.
    exists sp ; split ; [ | assumption].
    unfold allTuples.
    Search (In _ (TupleUtils.tuples_up_to_n _ _)).
    apply TupleUtils.tuples_up_to_n_incl_length.
    unfold isTuple in H1.
    auto.
  + destruct H as (ip & H1 & H2).
    econstructor ; [ eassumption | | ].
    - eapply p1 ; eassumption.
    - unfold allTuples in H1.
      Search (In _ (TupleUtils.tuples_up_to_n _ _)).
      eapply TupleUtils.tuple_length ; eassumption.
Qed.

Definition is_trace trans sm tra : Prop :=
  forall lk, List.In lk tra <-> in_trace trans sm lk.    
(* On aurait pu définir ensemble en compréhension. *)

Lemma p8 : forall trans sm, is_trace trans sm (compute_trace trans sm).
Proof.
  unfold is_trace.
  setoid_rewrite p7.
  tauto.
Qed.

(** * Apply link part of the r.h.s of rules (uses traces) **)

(* executable *)
Definition apply_link_pattern (tls:Trace) sm lk :list TargetLinkType := 
    lk.(linkPattern) (drop tls) (getIteration lk) sm (getSourcePiece lk) lk.(produced).

 (* predicative *)
Definition apply_link_pattern_rel tls sm lk tl : Prop := 
   List.In tl (lk.(linkPattern) (* fixme *) (drop tls) (getIteration lk) sm (getSourcePiece lk) lk.(produced)).
  

Lemma p9 : forall tls sm tlk lk,
  apply_link_pattern_rel tls sm tlk lk <-> List.In lk (apply_link_pattern tls sm tlk).
Proof.
  unfold apply_link_pattern.
  unfold apply_link_pattern_rel.
  tauto.
Qed.


(* executable *)
Definition applyTrLkOnModel (sm : SourceModel) (tra:Trace): list TargetLinkType :=
    flat_map (apply_link_pattern tra sm) tra. 

(* predicative *)
Inductive applyTrLkOnModel_rel (sm : SourceModel) (tra:Trace) (lk: TargetLinkType) : Prop :=
 | r6 : forall tlk, 
    List.In tlk tra -> 
    apply_link_pattern_rel tra sm tlk lk -> 
    applyTrLkOnModel_rel sm tra lk. 

Lemma p10 : forall sm tra lk,
  applyTrLkOnModel_rel sm tra lk <-> List.In lk (applyTrLkOnModel sm tra).
Proof.
  unfold applyTrLkOnModel.
  setoid_rewrite in_flat_map.
  setoid_rewrite <- p9. 
  intros ; split ; intro H.
  + inversion_clear H.
    eauto.
  + destruct H as (k & H1 & H2).
    econstructor ; eauto.
Qed.


(** * Execute **)

(* executable *)
Definition produced_elements := map TraceLink.produced.

(** Main definition below. *)

(* executable *)
Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  let t := compute_trace tr sm
  in
  {|
    modelElements := produced_elements t ;
    modelLinks := applyTrLkOnModel sm t
  |}.


(* predicative *)
Inductive is_produced_element tr sm : TargetElementType -> Prop :=
    | r7 : forall a b c, 
        in_trace tr sm {| source := a; produced := b; linkPattern := c |} ->
        is_produced_element tr sm b.

Lemma p11 : forall tr sm e,
  is_produced_element tr sm e <-> In e ( (execute tr sm).(modelElements)).
Proof.
  unfold execute.
  simpl modelElements.
  unfold produced_elements.
  Search (In _ (map _ _)).
  setoid_rewrite in_map_iff.
  setoid_rewrite <- p7.
  intros ; split ; intro H.
  + inversion_clear H.
    eexists ; split ; [ | eassumption]. reflexivity.  
  + destruct H as (k & H1 & H2).  
    destruct k.
    simpl in H1.
    subst.
    econstructor ; eassumption.
Qed.


Inductive is_produced_link tr sm (tl:TargetLinkType): Prop :=
    | r8 : forall tra, 
        is_trace tr sm tra ->
        applyTrLkOnModel_rel sm tra tl->
        is_produced_link tr sm tl.

(*
Lemma p12 : forall tr sm tl, 
  is_produced_link tr sm tl <-> In tl ( (execute tr sm).(modelLinks)).
Proof.
  unfold execute.
  simpl modelLinks.
  setoid_rewrite <- p10.
  intros ; split ; intro H.
  + inversion_clear H.
    
Qed.
*)

Definition is_result tr sm tm: Prop :=
  (forall e, (List.In e tm.(modelElements) <-> is_produced_element tr sm e)) /\ 
  (forall lk, (List.In lk tm.(modelLinks) <-> is_produced_link tr sm lk)).
(* On aurait pu définir un ensemble en compréhension. *)


End Semantics.

  
