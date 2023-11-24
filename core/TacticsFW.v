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






(* USED *)
(* Deprecated : use in_modelElements_inv instead. *)
Corollary in_trace_in_models_target {MM1:Metamodel} {T1} {T2} {BEQ} :
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
  intros.
  apply RichTraceLink.in_drop_inv in H. destruct H as (? & ? & ?).

  apply in_modelElements_inv. 
  unfold RichTraceLink.convert in H. inj H.
  exists x ; auto. 
Qed.


(* This is a weak version of Semantics.in_compute_trace_inv. *)
Lemma in_trace_split {tc:TransformationConfiguration} t m : 
  forall a, 
    In a (compute_trace t m) <-> 
      exists p : InputPiece,
        incl p (modelElements m) 
        /\ length p <= Syntax.arity t 
        /\ In a (traceTrOnPiece t m p).
Proof.
  intro.
  unfold compute_trace.
  setoid_rewrite in_flat_map at 1.
  setoid_rewrite Semantics.in_allTuples_incl.
  split.
  + intros (?&(?&?)&?).
    eexists ; repeat split ; eauto.
  + intros (? & ? & ? & ?).
    eexists ; repeat split ; eauto.
Qed.



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
  eapply transform_elements_fw ; [ | eassumption].  
  apply <- in_allTuples_incl_singleton. auto.
Qed.



