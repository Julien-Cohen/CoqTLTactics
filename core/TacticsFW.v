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
  apply RichTraceLink.in_drop_inv in H. simpl in H. destruct H as (? & ?).

  apply in_modelElements_inv. 
  unfold RichTraceLink.convert in H. 
  eexists ; split ; [ | eassumption] ; reflexivity.
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




Lemma transform_element_fw {tc} (t:Syntax.Transformation (tc:=tc)) cm e te  :
  0 < Syntax.arity t ->
  In e (modelElements cm) ->
  In te (produced_elements (traceTrOnPiece t cm [e])) ->
  In te (modelElements (execute t cm)).
Proof.
  intros A IN1 IN2.
  simpl.
  unfold compute_trace, produced_elements.
  rewrite map_flat_map. (* a trace can have several target elements *)
  apply List.in_flat_map. (* this is doing the job *)
  exists ([e]) ; split ; [ | auto ].
  apply <- in_allTuples_incl_singleton. auto.
Qed.

(* Used in Class2Relational *)
Ltac transform_element_fw_tac :=
  match goal with
    [ |- In _ (execute ?T _).(modelElements) ] =>
      eapply (transform_element_fw T) ; [ solve [compute ; auto ] | try eassumption | try (solve [simpl;auto])]
  end.



(** When we know which rule is the one we search, the following tactics help us to say it. 

In particular in the case we have an existential variable in the goal, as in [In ?r (Syntax.rules Class2Relational)]
(after use of [in_compute_trace_inv]).

*)
Lemma In_1 {A} :
      forall (e:A) s,
      (exists r, s = e :: r) -> In e s.
Proof.
  intros e s (r&E) ; subst s. 
  apply in_eq.
Qed.

Ltac first_in_list :=
  match goal with 
    [ |- In _ _ ] =>
      apply In_1 ; eexists ; reflexivity
  end.

Ltac first_rule :=
  match goal with 
    [ |- In _ (Syntax.rules _)] =>
      first_in_list
  end.

Lemma In_2 {A} :
      forall (e:A) s,
      (exists a r, s = a :: e :: r) -> In e s.
Proof.
  intros e s (a&r&E) ; subst s. 
  apply in_cons. apply in_eq.
Qed.

Ltac second_in_list :=
  match goal with 
    [ |- In _ _ ] =>
      apply In_2 ; eexists ; eexists ; reflexivity
  end.


Ltac second_rule :=
  match goal with 
    [ |- In _ (Syntax.rules _)] =>
      second_in_list
  end.



(** --------------------------------- *)

#[global]
Hint Unfold 
  Semantics.traceTrOnPiece 
  Semantics.traceRuleOnPiece 
  Semantics.traceIterationOnPiece 
  Semantics.traceElementOnPiece 
  Semantics.produced_elements 
  : trace.


(* fixme : a similar tactic exists *)
Ltac unfold_parse :=
  autounfold with parse.

Ltac unfold_trace :=
  autounfold with trace.

(* fixme : a similar tactic exists *)
Ltac unfold_accessors :=
  unfold Syntax.opu_name,
    ConcreteSyntax.e_name,
    ConcreteSyntax.e_outlink,
    ConcreteSyntax.e_OutKind,
    Syntax.opu_link.

Ltac incl_singleton :=
  apply incl_singleton ; eassumption.


Ltac transform_link_fw_tac r_num pat_num i :=
  match goal with
    [ |- In _ (execute _ _).(modelLinks) ] =>
      apply <- Semantics.in_modelLinks_inv ;
      setoid_rewrite Semantics.in_compute_trace_inv (*in the left part*) ;
      eexists ; split ; [ eexists ; split ; [ (*1*) | split ; [ (*2*)| eexists ; split ; [ (*3*)| split ; [ (*4*)| eexists ; split ; [ (*5*)| eexists ; split ; [ (*6*) |  eexists ; split ; [ (* 7 *)| (* 8*)] ] ] ] ] ] ] | (*9*)] ;
      [ | | | | | | reflexivity | | ] ;
      
      (* this works only for singletons *)
      [ incl_singleton | | | | | | | ] ;
      
      (* arity *)
      [ solve [simpl;auto] | | | | | | ] ;
      
      (* select the correct rule based on the hint received as parameter *) 
      [ match r_num with 1 => TacticsFW.first_rule | 2 => TacticsFW.second_rule end | | | | | ] ;
      
      (* if the user has selected the correct rule, the match guard should evaluate to true *)
      [ reflexivity | | | | ] ;
      
      (* iteration *)
      [ instantiate (1:=i) ; simpl ; solve [auto] | | | ] ; 
      
      (* which output pattern is concerned *)
      [  match pat_num with 1 => TacticsFW.first_in_list idtac | 2 => TacticsFW.second_in_list end | | ] ; 

      unfold_parse ; unfold_accessors ;
      
      (* identify the instanciation of the out pattern *)
      [ try reflexivity (* sometimes needs a rewrite *)| ]
        
  end.
