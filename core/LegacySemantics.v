
Require Semantics.
Import TransformationConfiguration Syntax UserExpressions TraceLink List Utils.

(** * Old Semantics for link generation *)

(** We keep the old semantics for compatibility with the [TransformationEngine] class (see [Certification]).*)

Definition applyUnitOnPiece {tc:TransformationConfiguration}
            (opu: OutputPatternUnit)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: InputPiece) (iter: nat) : list TargetLinkType :=
  match (evalOutputPatternUnit opu sm sp iter) with 
  | Some l => evalOutputPatternLink sm sp l iter (drop (Semantics.compute_trace tr sm)) opu
  | None => nil
  end.

Definition applyIterationOnPiece {tc:TransformationConfiguration} (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: InputPiece) (iter: nat) : list TargetLinkType :=
  flat_map (fun o => applyUnitOnPiece o tr sm sp iter)
    r.(r_outputPattern).

Definition applyRuleOnPiece {tc:TransformationConfiguration} (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: InputPiece): list TargetLinkType :=
  flat_map (applyIterationOnPiece r tr sm sp)
    (seq 0 (evalIterator r sm sp)).

Definition applyTrOnPiece {tc:TransformationConfiguration} (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list TargetLinkType :=
  flat_map (fun r => applyRuleOnPiece r tr sm sp) (Semantics.matchingRules tr sm sp).

Definition applyTrLkOnModel_old {tc:TransformationConfiguration} (tr: Transformation) (sm : SourceModel) 
  : list TargetLinkType
  :=  flat_map (applyTrOnPiece tr sm) (Semantics.allTuples tr sm).



(** Equivalence between the old semantics for links and the current one. *)
Lemma exploit_in_compute_trace {tc:TransformationConfiguration} tr sm :
  forall tlk,
    In tlk (Semantics.compute_trace tr sm) <-> 
    exists r  opu, 
    In (getSourcePiece tlk) (Semantics.allTuples tr sm) 
    /\ In r (Semantics.matchingRules tr sm (getSourcePiece tlk))
    /\ In (getIteration tlk) (seq 0 (evalIterator r sm (getSourcePiece tlk) )) 
    /\ In opu (r_outputPattern r) 
    /\ opu.(opu_element)  (getIteration tlk) sm (getSourcePiece tlk)  = return tlk.(produced)
    /\ tlk.(linkPattern) = opu.(opu_link)
    /\ getName tlk = opu.(opu_name).
Proof.
  intro ; split ; intro H.
{  
  unfold Semantics.compute_trace.
    apply in_flat_map in H. destruct H as (ip, (IN1, IN2)).
  unfold Semantics.traceTrOnPiece in IN2.
  apply in_flat_map in IN2. destruct IN2 as (r, (IN2, IN3)).
  unfold Semantics.traceRuleOnPiece in IN3.
  apply in_flat_map in IN3.
  destruct IN3 as (i, (IN3,IN4)).
  unfold Semantics.traceIterationOnPiece in IN4.
  apply in_flat_map in IN4. destruct IN4 as (opu, (IN4,IN5)).
  apply in_optionToList in IN5.
  unfold Semantics.traceElementOnPiece in IN5.
  monadInv IN5.
  unfold getSourcePiece. simpl.
  unfold evalOutputPatternUnit in IN5.
  eauto 11.
}
{  

  destruct H as (r, (opu, (H1, (H2, (H3, (H4, (H5, (H6, H7)))))))). 
  
  unfold Semantics.applyTrLkOnModel.  apply in_flat_map.
  exists (getSourcePiece tlk).
  split ; [ assumption|  ].
  unfold applyTrOnPiece.  apply in_flat_map.
  exists r.
  split ; [ assumption | ].
  unfold applyRuleOnPiece.  apply in_flat_map.
  exists (getIteration tlk).
  split ; [ assumption | ].
  unfold applyIterationOnPiece.  apply in_flat_map.
  exists opu.
  split ; [ assumption | ].
  unfold Semantics.traceElementOnPiece.
  unfold evalOutputPatternUnit.
  rewrite H5.
  simpl.
  rewrite <- H7.
  rewrite <- H6.
  left.
  
  
  destruct tlk. 
  destruct source.
  destruct p. auto.
}
Qed.

Lemma included_left {tc:TransformationConfiguration} tr sm :
  incl  (Semantics.applyTrLkOnModel sm (Semantics.compute_trace tr sm))  (applyTrLkOnModel_old tr sm).
Proof.
  intro link.
  unfold Semantics.applyTrLkOnModel.
  intro H.
  apply in_flat_map in H. destruct H as (trl, (IN1, IN2)).

  apply (exploit_in_compute_trace) in IN1. 
   destruct IN1 as  (r, (opu, (E1, (E2, (E3, (E4, (E5, (E6, E7)))))))).

  unfold Semantics.applyTrLkOnModel.  apply in_flat_map.
  exists (getSourcePiece trl).
  split ; [ assumption|  ].
  unfold applyTrOnPiece.  apply in_flat_map.
  exists r.
  split ; [ assumption | ].
  unfold applyRuleOnPiece.  apply in_flat_map.
  exists (getIteration trl).
  split ; [ assumption | ].
  unfold applyIterationOnPiece.  apply in_flat_map.
  exists opu.
  split ; [ assumption | ].
  unfold applyUnitOnPiece.
  unfold evalOutputPatternUnit.
  rewrite E5.
  unfold evalOutputPatternLink.
  destruct trl ; simpl in *.
  unfold getSourcePiece in *.
  unfold getIteration in *.
  unfold getName in *.
  simpl in *.
  subst.
  destruct source ; simpl in *.
  destruct p ; simpl in *.
  subst.
  exact IN2.
Qed.

Lemma included_right {tc:TransformationConfiguration} tr sm :
  incl (applyTrLkOnModel_old tr sm) (Semantics.applyTrLkOnModel sm (Semantics.compute_trace tr sm)).
Proof.
  intro link.
  intro H.
  unfold Semantics.applyTrLkOnModel.
  apply in_flat_map.
  unfold Semantics.applyTrLkOnModel in H.
  apply in_flat_map in H. destruct H as (ip, (H1,H2)).
  unfold applyTrOnPiece in H2.
  apply in_flat_map in H2. destruct H2 as (r, (H3,H4)).
  unfold applyRuleOnPiece in H4.
  apply in_flat_map in H4. destruct H4 as (i, (H5,H6)).
  unfold applyIterationOnPiece in H6.
  apply in_flat_map in H6. destruct H6 as (opu, (H7,H8)).
  unfold applyUnitOnPiece in H8.
  destruct (evalOutputPatternUnit opu sm ip i) eqn:E ; [ | crush ].

  destruct opu ; simpl in *.
  exists ({| source := (ip, i, opu_name) ; produced := t ; linkPattern := opu_link |} ). 
  simpl.
  unfold getIteration ; simpl.
  unfold getSourcePiece ; simpl.
  split ; [ | assumption ].
  
  apply exploit_in_compute_trace.

  exists r.
  eexists.
  unfold linkPattern, getName, getSourcePiece, getIteration, source, produced.
  repeat (split ; eauto ).
Qed.

Lemma equiv {tc:TransformationConfiguration} tr sm :
  forall lk, In lk (applyTrLkOnModel_old tr sm) <-> In lk (Semantics.applyTrLkOnModel sm (Semantics.compute_trace tr sm)).
Proof.
  intro link.
  split.
  apply included_right.
  apply included_left.
Qed.

(** FIXME : move-me to Certification ? *)
(* FIXME : never used *)
Lemma in_applyUnitOnPiece {A B C D} :
  forall (tr:Transformation (tc:=Build_TransformationConfiguration A (Metamodel.Build_Metamodel B C D))) 
         a opu sm sp it,
  In a (applyUnitOnPiece opu tr sm sp it) ->
  exists g, 
    evalOutputPatternUnit opu sm sp it = Some g
    /\ In a (evalOutputPatternLink sm sp g it (drop (Semantics.compute_trace tr sm)) opu).
Proof.  
  unfold applyUnitOnPiece.
  intros until it ; intro IN.
  PropUtils.destruct_match_H IN ; [ | contradiction IN].
  eauto.
Qed.


