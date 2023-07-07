Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import TransformationConfiguration.
Require Import UserExpressions.

Require Import RichTraceLink.

Notation elements_proj := (map RichTraceLink.produced).

Section Semantics.

Context {tc: TransformationConfiguration}.

(** * Pattern matching *)

Definition allTuples (tr: Transformation) (sm : SourceModel) : list InputPiece :=
  tuples_up_to_n sm.(modelElements) tr.(arity).

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

Definition traceIterationOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) (iter: nat) :  RichTraceLink.Trace :=
  flat_map (fun o => optionToList (traceElementOnPiece o sm sp iter))
    r.(r_outputPattern).

Definition traceRuleOnPiece (r: Rule) (sm: SourceModel) (sp: InputPiece) :  RichTraceLink.Trace :=
  flat_map (traceIterationOnPiece r sm sp)
    (seq 0 (evalIterator r sm sp)).

Definition traceTrOnPiece (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : RichTraceLink.Trace :=
  flat_map (fun r => traceRuleOnPiece r sm sp) (matchingRules tr sm sp).



Definition traceTrOnModel (tr: Transformation) (sm : SourceModel) :  RichTraceLink.Trace :=
  flat_map (traceTrOnPiece tr sm) (allTuples tr sm).  


(** * Apply link part of the r.h.s of rules (uses traces) **)

Definition applyTrOnModel (sm : SourceModel) (tls:Trace): list TargetLinkType :=
  flat_map 
    (fun lk => lk.(linkPattern) (drop tls) (getIteration lk) sm (getSourcePattern lk) lk.(produced)) 
    tls. 




(** * Execute **)


Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
  let t := traceTrOnModel tr sm
  in
  {|
    modelElements := elements_proj t ;
    modelLinks := applyTrOnModel sm t
  |}.

End Semantics.



(** * Some tactics *)

(* tactics need to be outside the section to be visible *)


Ltac exploit_in_allTuples H :=
  match type of H with 
    In _ (allTuples _ _) => 
      unfold allTuples in H ; 
      apply tuples_up_to_n_incl in H ;
      ListUtils.incl_inv H
  end.

Ltac in_allTuples_auto :=
  match goal with 
    [ H : In _ (allTuples _ _) |- _ ] =>
       exploit_in_allTuples H
  end.

(** * Old Semantics for link generation *)

(** We keep the old semantics for compatibility with the [TransformationEngine] class (see [Certification]).*)

Definition applyUnitOnPiece {tc:TransformationConfiguration}
            (opu: OutputPatternUnit)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: InputPiece) (iter: nat) : list TargetLinkType :=
  match (evalOutputPatternUnit opu sm sp iter) with 
  | Some l => evalOutputPatternLink sm sp l iter (drop (traceTrOnModel tr sm)) opu
  | None => nil
  end.

Definition applyIterationOnPiece {tc:TransformationConfiguration} (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: InputPiece) (iter: nat) : list TargetLinkType :=
  flat_map (fun o => applyUnitOnPiece o tr sm sp iter)
    r.(r_outputPattern).

Definition applyRuleOnPiece {tc:TransformationConfiguration} (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: InputPiece): list TargetLinkType :=
  flat_map (applyIterationOnPiece r tr sm sp)
    (seq 0 (evalIterator r sm sp)).

Definition applyTrOnPiece {tc:TransformationConfiguration} (tr: Transformation) (sm : SourceModel) (sp: InputPiece) : list TargetLinkType :=
  flat_map (fun r => applyRuleOnPiece r tr sm sp) (matchingRules tr sm sp).

Definition applyTrOnModel_old {tc:TransformationConfiguration} (tr: Transformation) (sm : SourceModel) 
  : list TargetLinkType
  :=  flat_map (applyTrOnPiece tr sm) (allTuples tr sm).



(** Equivalence between the old semantics for links and the current one. *)
Lemma exploit_in_traceTrOnModel {tc:TransformationConfiguration} tr sm :
  forall tlk,
    In tlk (traceTrOnModel tr sm) <-> 
    exists r  opu, 
    In (getSourcePattern tlk) (allTuples tr sm) 
    /\ In r (matchingRules tr sm (getSourcePattern tlk))
    /\ In (getIteration tlk) (seq 0 (evalIterator r sm (getSourcePattern tlk) )) 
    /\ In opu (r_outputPattern r) 
    /\ opu.(opu_element)  (getIteration tlk) sm (getSourcePattern tlk)  = return tlk.(produced)
    /\ tlk.(linkPattern) = opu.(opu_link)
    /\ getName tlk = opu.(opu_name).
Proof.
  intro ; split ; intro H.
{  
  unfold traceTrOnModel.
    apply in_flat_map in H. destruct H as (ip, (IN1, IN2)).
  unfold traceTrOnPiece in IN2.
  apply in_flat_map in IN2. destruct IN2 as (r, (IN2, IN3)).
  unfold traceRuleOnPiece in IN3.
  apply in_flat_map in IN3.
  destruct IN3 as (i, (IN3,IN4)).
  unfold traceIterationOnPiece in IN4.
  apply in_flat_map in IN4. destruct IN4 as (opu, (IN4,IN5)).
  apply in_optionToList in IN5.
  unfold traceElementOnPiece in IN5.
  monadInv IN5.
  unfold getSourcePattern. simpl.
  unfold evalOutputPatternUnit in IN5.
  eauto 11.
}
{  

  destruct H as (r, (opu, (H1, (H2, (H3, (H4, (H5, (H6, H7)))))))). 
  
  unfold applyTrOnModel.  apply in_flat_map.
  exists (getSourcePattern tlk).
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
  unfold traceElementOnPiece.
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

Lemma included_1 {tc:TransformationConfiguration} tr sm :
  incl  (applyTrOnModel sm (traceTrOnModel tr sm))  (applyTrOnModel_old tr sm).
Proof.
  intro link.
  unfold applyTrOnModel.
  intro H.
  apply in_flat_map in H. destruct H as (trl, (IN1, IN2)).

  apply (exploit_in_traceTrOnModel) in IN1. 
   destruct IN1 as  (r, (opu, (E1, (E2, (E3, (E4, (E5, (E6, E7)))))))).

  unfold applyTrOnModel.  apply in_flat_map.
  exists (getSourcePattern trl).
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
  unfold getSourcePattern in *.
  unfold getIteration in *.
  unfold getName in *.
  simpl in *.
  subst.
  destruct source ; simpl in *.
  destruct p ; simpl in *.
  subst.
  exact IN2.
Qed.

Lemma included_2 {tc:TransformationConfiguration} tr sm :
  incl (applyTrOnModel_old tr sm) (applyTrOnModel sm (traceTrOnModel tr sm)).
Proof.
  intro link.
  intro H.
  unfold applyTrOnModel.
  apply in_flat_map.
  unfold applyTrOnModel in H.
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
  unfold getSourcePattern ; simpl.
  split ; [ | assumption ].
  
  apply exploit_in_traceTrOnModel.

  exists r.
  eexists.
  unfold linkPattern, getName, getSourcePattern, getIteration, source, produced.
  repeat (split ; eauto ).
Qed.

Lemma included_3 {tc:TransformationConfiguration} tr sm :
  forall lk, In lk (applyTrOnModel_old tr sm) <-> In lk (applyTrOnModel sm (traceTrOnModel tr sm)).
Proof.
  intro link.
  split.
  apply included_2.
  apply included_1.
Qed.


(** FIXME : move-me to Certification ? *)
Lemma in_applyUnitOnPiece {A B C D} :
  forall (tr:Transformation (tc:=Build_TransformationConfiguration A (Metamodel.Build_Metamodel B C D))) 
         a opu sm sp it,
  In a (applyUnitOnPiece opu tr sm sp it) ->
  exists g, 
    evalOutputPatternUnit opu sm sp it = Some g
    /\ In a (evalOutputPatternLink sm sp g it (drop (traceTrOnModel tr sm)) opu).
Proof.  
  unfold applyUnitOnPiece.
  intros until it ; intro IN.
  PropUtils.destruct_match IN ; [ | contradiction IN].
  eauto.
Qed.


Ltac exploit_In_applyUnitOnPiece H NEWNAME :=
  match type of H with
    | In _ (applyUnitOnPiece _ _ _ _ _) =>
        apply in_applyUnitOnPiece in H ;
        destruct H as (? & (NEWNAME & H))
end.
