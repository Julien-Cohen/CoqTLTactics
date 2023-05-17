Require Import String.
Require Import List.

Require Import core.utils.Utils.
Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.


From transformations.Class2Relational_TUPLE_SP
  Require
(*  ClassModelProperties 
  RelationalModelProperties *)
  C2RTactics
  Class2Relational_TUPLE_SP.


Import Class2Relational_TUPLE_SP ClassMetamodel RelationalMetamodel.




(** *** Utilities on transformation of elements *)

Lemma in_allTuples_2 :
      forall a b m t,
        t.(Syntax.arity) >= 2 ->
        In a (modelElements m) ->
        In b (modelElements m) ->
        In [a;b] (allTuples t m).
Proof.
  intros until t ; intros HA IN1 IN2.
  unfold allTuples.
  apply TupleUtils.tuples_up_to_n_incl_length.
  {
    apply List.incl_cons ; auto.
    apply List.incl_cons ; auto.
    apply List.incl_nil_l.
  }
  {
    simpl.
    auto with arith.
  }
Qed.

Lemma transform_attribute_fw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational_TUPLE_SP cm ->
  (* precondition *)  forall id name id_c name_c,
    In (AttributeElement {| attr_id:= id ; derived := false ; attr_name := name|}) cm.(modelElements) ->    
    In (ClassElement {| class_id:= id_c ; class_name := name_c |}) cm.(modelElements) ->
    getAttributeType
      {| attr_id := id; derived := false; attr_name := name |} cm = Some {| class_id := id_c; class_name := name_c |} ->
  (* postcondition *) 
    In (ColumnElement {| column_id := id; column_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros i n i2 n2 H1 H2 H3.
  simpl.

  apply List.in_flat_map.
  exists ([AttributeElement
            {| attr_id := i; derived := false; attr_name := n |} ; ClassElement {| class_id := i2; class_name := n2 |} ]).
  split. 
  { 
    apply in_allTuples_2 ; auto.
  }
  {
    unfold instantiatePattern.
    apply List.in_flat_map.

    match eval cbv beta iota fix 
            delta [Class2Relational_TUPLE_SP 
                     Class2Relational_TUPLE_SP'
                     Parser.parse
                     List.nth_error
                     Syntax.rules
                     List.map
                     ConcreteSyntax.ConcreteTransformation_getConcreteRules] 
          in (List.nth_error Class2Relational_TUPLE_SP.(Syntax.rules) 1 (* second rule *)) 
    with 
    | Some ?r => remember r as R ; exists R
    | None => fail
    | ?other => remember other as R 
    end.

    split ; [  | ]. 
    { 
      unfold matchingRules ; simpl.
      
      unfold ConcreteExpressions.makeGuard ; simpl.
      rewrite H3 ; simpl.
      rewrite beq_Class_refl. 
      subst R ; apply in_eq.
    }

    {
      unfold instantiateRuleOnPattern.
      simpl.
      unfold EvalExpressions.evalIteratorExpr.
      rewrite HeqR at 2 ; simpl.
      rewrite List.app_nil_r.
      unfold instantiateIterationOnPattern ; simpl.
      rewrite HeqR ; unfold Syntax.r_outputPattern ; simpl.
      auto.
    }
  }
Qed.


Lemma transform_class_fw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational_TUPLE_SP cm ->
  (* precondition *)  forall id name,
    In (ClassElement {| class_id:= id ; class_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (TableElement {| table_id := id; table_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros i n H.
  simpl.
  apply C2RTactics.allModelElements_allTuples in H.
  revert H ; generalize (allTuples Class2Relational_TUPLE_SP cm).

  intros s H.
  apply List.in_flat_map.
  eexists ; split ; [exact H | clear H ].
  simpl ; auto.

Qed.




Lemma transform_attribute_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational_TUPLE_SP cm ->
  (* precondition *)  forall id name,
      In (ColumnElement {| column_id := id; column_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (AttributeElement {| attr_id:= id ; derived := false ; attr_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst.
  intros i n H.

  (* (1) *)
  destruct (Tactics.destruct_in_modelElements_execute_lem H) 
    as (r & sp & nn & ope & IN_E & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & H'). 

  (* (2) *)
  Tactics.progress_in_In_rules IN_RULE ; [ exfalso | ] ;

  (* (3) make the ouput-pattern-element appear *)
  Tactics.progress_in_In_outpat IN_OP ;

  (* (4) *) 
  (* needed here to get that derived = false *)
  Tactics.exploit_evalGuard MATCH_GUARD ; 
  
  (* (5.E) make the matched element appear *)
  Tactics.exploit_evaloutpat H' ;

  (* (6) *)
  (* not useful here *) 
  Tactics.exploit_in_it IN_IT ;

  (* (7) *)
  Semantics.exploit_in_allTuples IN_E.
  

  C2RTactics.exploit_guard MATCH_GUARD.

  destruct t1 ; simpl in *. subst derived. 
  exact IN_E.
Qed.


Lemma transform_class_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational_TUPLE_SP cm ->
  (* precondition *)  forall id name,
      In (TableElement {| table_id := id; table_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (ClassElement {| class_id:= id ; class_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst.
  intros i n H.

  (* (1) *)
  destruct (Tactics.destruct_in_modelElements_execute_lem H) 
    as (r & sp & nn & ope & IN_E & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & H'). 

  (* (2) *)
  Tactics.progress_in_In_rules IN_RULE ; [ | exfalso ] ; 

  (* (3) *)
  Tactics.progress_in_In_outpat IN_OP ;
  
  (* (4) *)
  (* not useful here *)
  Tactics.exploit_evalGuard MATCH_GUARD ; 

  (* (5.E) *)
  Tactics.exploit_evaloutpat H' ;

  (* (6) *)
  (* not useful here *) 
  Tactics.exploit_in_it IN_IT ;
  
  (* (7) *)
  Semantics.exploit_in_allTuples IN_E.
  
  destruct t0 ; exact IN_E.

Qed.
