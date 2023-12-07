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


(*Ltac incl_singleton :=
  apply ListUtils.incl_singleton ; eassumption.
*)
Ltac incl_singleton :=
  apply ListUtils.incl_singleton ; 
  multimatch goal with
    [ H : List.In _ _ |- _ ] => exact H 
                                    
    (* multimatch is important here because it allows backtracking, as opposed to eassumption. Here, if there are two hypothsesi in the context that allow to solve the goal, because of evar in the goal, if the the selected hypothesis instanciates the evar so that the following tactics fail, it will backtrack and select another one.  This situation can be explored in the proof of Moore2MEaly/theorems/Links/source_link_fw (use move to switch the order of hypothesis) *)

  end.

Ltac rule_number n := 
  match n with 
    1 => TacticsFW.first_rule 
  | 2 => TacticsFW.second_rule 
end.

Ltac pattern_number n :=
  match n with 
    1 => TacticsFW.first_in_list 
  | 2 => TacticsFW.second_in_list 
  end.


Ltac transform_link_fw_tac_singleton r_num pat_num i :=
  match goal with
    [ |- In _ (Semantics.execute _ _).(modelLinks) ] =>
      apply <- Semantics.in_modelLinks_inv ;
      setoid_rewrite Semantics.in_compute_trace_inv (*in the left part*) ;
      eexists ; eexists i ; eexists ; eexists ; eexists ;
      split ; [ split ; [ (*1*) | split ; [ (* 2 *)|  eexists ; split ; [ (* 3 *) | split ; [(* 4 *)| split ; [ (* 5 *) |  eexists ; split ; [ (*6*) | (*7*)] ]]] ] ] |  (* 8 *)] ;


      (* fix the rule under concern following user hint *)
      [  | | solve [rule_number r_num] | | | | | ] ;

      [ | | | | | | ] ;

      (* fix the output pattern in the rule following user hint *)
      [ | | | | solve [pattern_number pat_num] | | ] ;
      
      [ | | | | | ] ;

      (* the the source piece using the context *)
      (* fragile : select the first element in the context instead of the good one *)
      [ solve [TacticsFW.incl_singleton] | | | | | ] ; (* this works only for singletons *)

      [ | | | | ] ;

      (* solve the arity contraint (the input is fixed) *)
      [ solve [simpl;auto] | | | | ] ;

      (* Solve the guard (the input is fixed) *)
      (* If the user has selected the correct rule, the match guard should evaluate to true *)
      [ reflexivity | | | ] ;
      
      [ | | ] ;
      
      (* solve the iteration contraint *)
      [ solve [ simpl ; auto] | | ] ;

      [ | ] ; 
      try reflexivity ;
      autounfold with 
        parse 
        ConcreteOutputPatternUnit_accessors 
        opu_accessors 

(* FIXME : change the order of the terms in Semantics.in_compute_trace_inv so that the order of the subgoals to solve smartly is left to right *)

  end.
