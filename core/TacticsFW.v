Require Import core.Semantics.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Require Certification.

Import Metamodel Model.



(** * Tactic to transform an hypothesis H : In [e] (allTuples _ cm)
    into H: In (e) (modelElements cm)
*)


Lemma allModelElements_allTuples {tc:TransformationConfiguration} e t cm: 
  In e cm.(modelElements) ->
  0 < Syntax.arity t ->
  In [e] (allTuples t cm).
Proof. 
  intros.
  apply Certification.allTuples_incl_length.
   + apply incl_singleton. assumption.
   + compute. auto.
Qed.

(* USED *)
Lemma in_trace_in_models_target {MM1:Metamodel} {T1} {T2} {BEQ} :
  forall 
    (t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ)))
    m s e,
    In {| 
        PoorTraceLink.source := s ;
        PoorTraceLink.produced := e
      |}
      (RichTraceLink.drop (compute_trace t m)) ->
    In e (execute t m).(modelElements).
Proof.
  intros t m s e IN.
  unfold execute. 
  unfold modelElements. 
  unfold RichTraceLink.drop in IN.
  apply in_map_iff. 
  apply in_map_iff in IN. 
  destruct IN as (x & C & IN). 
  exists x. 
  split ; [ | assumption ]. 
  destruct x ; unfold RichTraceLink.convert in C. 
  congruence.
Qed.



(** NOT USED *) 
Lemma in_modelElements_execute_left {MM1} {T1} {T2} {BEQ} :
  forall 
    {t: Syntax.Transformation (tc:=Build_TransformationConfiguration MM1 (Build_Metamodel T1 T2 BEQ))} 
    m e,
    
  forall r s i opu,
    In s (allTuples t m) ->
    In r (Syntax.rules t) ->
    UserExpressions.evalGuard r m s = true ->
    In i (seq 0 (UserExpressions.evalIterator r m s)) ->
    In opu (Syntax.r_outputPattern r) ->
    UserExpressions.evalOutputPatternUnit opu m s i = Some e ->
    In e (modelElements (execute t m)).
Proof.
  intros. 
  apply Certification.tr_execute_in_elements.
  exists s. split ; [assumption | ].
  apply Certification.tr_instantiateOnPiece_in. (* FIXME : name incoherence *)
  exists r. 
  split.
  + apply Certification.tr_matchingRules_in. split ; assumption.
  + apply Certification.tr_instantiateRuleOnPiece_in.
    exists i.
    split ; [ assumption | ].
    apply Certification.tr_instantiateIterationOnPiece_in.
    exists opu. split ; [ assumption | ].
    rewrite Certification.tr_instantiateElementOnPiece_leaf.
    assumption.
Qed.



Ltac destruct_in_trace_G :=
  match goal with 
    [ |- In _ (compute_trace _ _)] => 
      unfold compute_trace ;
      apply in_flat_map
  end.



Lemma transform_elements_fw {tc} cm p tp (t:Syntax.Transformation (tc:=tc)) :
  In p (allTuples t cm) ->
  In tp (elements_proj (traceTrOnPiece t cm p)) ->
  In tp (modelElements (execute t cm)).
Proof.
  intros IN1 IN2.
  simpl.
  unfold compute_trace.
  rewrite map_flat_map. (* a trace can have several target elements *)
  apply List.in_flat_map. (* this is doing the job *)
  eauto.
Qed.

(* Used in Class2Relational *)
Lemma transform_element_fw {tc} cm e te (t:Syntax.Transformation (tc:=tc)) :
  0 < Syntax.arity t ->
  In e (modelElements cm) ->
  In te (elements_proj (traceTrOnPiece t cm [e])) ->
  In te (modelElements (execute t cm)).
Proof.
  intros A IN1 IN2.
  eapply allModelElements_allTuples in IN1 ; [ | exact A]. (* from element to singleton *)
  eapply transform_elements_fw ; eassumption.
Qed.


Lemma in_links_fw tc cm (t:Syntax.Transformation (tc:=tc)):
  forall (sp:InputPiece) (r:Syntax.Rule) i opu produced_element,

    incl sp (modelElements cm) ->
    
    Datatypes.length sp <= Syntax.arity t ->
    
    In r t.(Syntax.rules)  ->
    
    UserExpressions.evalGuard r cm sp = true ->
    
    In i (seq 0 (UserExpressions.evalIterator r cm sp)) ->
    
    In opu (Syntax.r_outputPattern r) ->
    
    UserExpressions.evalOutputPatternUnit opu cm sp i = Some produced_element ->
    
    
    forall l,
      In l  (UserExpressions.evalOutputPatternLink cm sp produced_element i (RichTraceLink.drop(compute_trace t cm)) opu) ->
      In l (modelLinks (execute t cm)).
Proof.
  intros sp r i opu produced_element.
  intros IN_MOD A IN_R EVAL_GUARD  EVAL_IT IN_OPU  EVAL_OUT_EL lk. 
  intro INLV.

  apply Certification.tr_execute_in_links.

  exists sp.  
  split.
  
  { apply Certification.allTuples_incl_length ; [ exact IN_MOD | exact A]. }
  
  {
    apply Certification.tr_applyOnPiece_in.
    exists r.
    split.
    {
      apply Certification.tr_matchingRules_in.
      split ; [ exact IN_R | exact EVAL_GUARD].
    }
    {
      apply Certification.tr_applyRuleOnPiece_in.
      exists i.
      split.
      { exact EVAL_IT. }
      { 
        apply Certification.tr_applyIterationOnPiece_in.
        exists opu.
        split.
        { exact IN_OPU. }
        { 
          rewrite Certification.tr_applyUnitOnPiece_leaf with (te:=produced_element).
          { exact INLV. }
          { exact EVAL_OUT_EL. }
        }
      }
    }
  }
Qed.
