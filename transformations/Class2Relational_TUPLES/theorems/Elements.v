Require Import String.
Require Import List.
Open Scope string_scope.

Require Import core.utils.Utils.
Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require        usertools.TacticsBW.

From transformations.Class2Relational_TUPLES
  Require
  C2RTactics
  Class2Relational_TUPLES.


Import Class2Relational_TUPLES ClassMetamodel RelationalMetamodel.


(** Forward results *)


Lemma transform_attribute_fw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational_TUPLES cm ->
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

  TacticsFW.in_modelElements_pair_fw_tac "Attribute2Column" "col" 0 H1 H2 ;
  try reflexivity ; [].

  (* complex guard *) 
  unfold ConcreteExpressions.makeGuard.
  unfold ConcreteExpressions.wrap.
  unfold toEData.
  unfold unbox.
  simpl.
  rewrite H3.
  simpl.
  rewrite ClassMetamodel.internal_nat_dec_lb ; auto.
  rewrite ClassMetamodel.internal_string_dec_lb ; auto.
Qed.



(* without tactic *)
Lemma transform_attribute_fw_notactic : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational_TUPLES cm ->
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
  unfold compute_trace, produced_elements.
  rewrite map_flat_map.
  apply List.in_flat_map.
  exists ([AttributeElement
            {| attr_id := i; derived := false; attr_name := n |} ; ClassElement {| class_id := i2; class_name := n2 |} ]).
  split. 
  { 
    apply (SemanticsTools.in_allTuples_pair Class2Relational_TUPLES) ; auto.
  }
  {
    unfold traceTrOnPiece.
    rewrite map_flat_map.
    apply List.in_flat_map.

    match eval cbv beta iota fix 
            delta [Class2Relational_TUPLES 
                     Class2Relational_TUPLES'
                     Parser.parse
                     List.nth_error
                     Syntax.rules
                     List.map
                     ConcreteSyntax.concreteRules] 
          in (List.nth_error Class2Relational_TUPLES.(Syntax.rules) 1 (* second rule *)) 
    with 
    | Some ?r => remember r as R ; exists R
    | None => fail
    | ?other => remember other as R 
    end.

    split ; [  | ]. 
    { 
      unfold matchingRules ; simpl.
      
      unfold ConcreteExpressions.makeGuard ; simpl.
      rewrite H3. unfold is_option_eq. 
      rewrite internal_Class_t_dec_lb ; auto. 
      subst R. apply in_eq.
    }

    {
      unfold traceRuleOnPiece.
      rewrite map_flat_map.
      simpl.
      unfold UserExpressions.evalIterator.
      rewrite HeqR at 1 ; simpl.
      rewrite List.app_nil_r.
      rewrite HeqR ; unfold Syntax.r_outputPattern ; simpl.
      auto.
    }
  }
Qed.

Lemma transform_class_fw_notactic : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational_TUPLES cm ->
  (* precondition *)  forall id name,
    In (ClassElement {| class_id:= id ; class_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (TableElement {| table_id := id; table_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros i n H.
  simpl.
  unfold compute_trace, produced_elements. 
  apply C2RTactics.allModelElements_allTuples in H.
  revert H ; generalize (allTuples Class2Relational_TUPLES cm).

  intros s H.
  rewrite map_flat_map.
  apply List.in_flat_map.
  eexists ; split ; [exact H | clear H ].
  simpl ; auto.

Qed.

Lemma transform_class_fw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational_TUPLES cm ->
  (* precondition *)  forall id name,
    In (ClassElement {| class_id:= id ; class_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (TableElement {| table_id := id; table_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros i n H.  

  (* Simple resolution (not the general case) *)
  Succeed solve [TacticsFW.transform_element_fw_tac].

  (* More general resolution *)
  TacticsFW.in_modelElements_singleton_fw_tac "Class2Table" "tab" 0 H ; reflexivity. 
Qed.


(** Backward results *)

Lemma transform_attribute_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational_TUPLES cm ->
  (* precondition *)  forall id name,
      In (ColumnElement {| column_id := id; column_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (AttributeElement {| attr_id:= id ; derived := false ; attr_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst.
  intros i n H.

  TacticsBW.exploit_element_in_result H ; [] ; 

  C2RTactics.exploit_guard MATCH_GUARD.

  destruct e ; simpl in *. subst derived. 
  assumption.
Qed.


Lemma transform_class_bw : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational_TUPLES cm ->
  (* precondition *)  forall id name,
      In (TableElement {| table_id := id; table_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (ClassElement {| class_id:= id ; class_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst.
  intros i n H.
  
  TacticsBW.exploit_element_in_result H ; []. 

  
  destruct e ; assumption.

Qed.
