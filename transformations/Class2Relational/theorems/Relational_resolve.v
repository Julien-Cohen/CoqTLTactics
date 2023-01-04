Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.

Require Import core.utils.Utils.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From transformations.Class2Relational Require Tactics.

(** *** Utilities on transformation of elements *)

(* FIXME : move-me *)
(* NOT USED *)
Lemma transform_attribute : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
    In (AttributeElement {| attr_id:= id ; derived := false ; attr_name := name|}) cm.(modelElements) ->
  (* postcondition *) 
    In (ColumnElement {| column_id := id; column_name := name |}) (rm.(modelElements)). 
Proof.
  intros cm rm H ; subst.
  intros i n H.
  simpl.
  apply Tactics.allModelElements_allTuples in H.
  revert H ; generalize (allTuples Class2Relational cm).
  induction l ; intro H ; [ solve [inversion H] | simpl ].
  apply List.in_or_app.
  simpl in H.
  destruct_or H ; [ left | right ].
  + subst.
    clear IHl.
    compute.
    left.
    reflexivity.
  + auto. 
Qed.

(* FIXME : move-me *)
(* NOT USED *)
Lemma transform_attribute_back : 
  forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  forall id name,
      In (ColumnElement {| column_id := id; column_name := name |}) (rm.(modelElements)) ->
  (* postcondition *) 
    In (AttributeElement {| attr_id:= id ; derived := false ; attr_name := name|}) (cm.(modelElements))
. 
Proof.
  intros cm rm H ; subst.
  intros i n H.
  simpl in H.
  apply Tactics.allModelElements_allTuples_back with (t:=Class2Relational).
  revert H ; generalize (allTuples Class2Relational cm).
  induction l ; intro H ; [ solve [inversion H] | simpl ].
  simpl in H.
  apply List.in_app_or in H.

  destruct_or H ; [ left | right ].
  + Tactics.show_singleton.
    Tactics.show_origin.
    f_equal.
    f_equal.
    destruct a.
    destruct derived ; compute in H.
    - contradiction.
    - remove_or_false H.
      injection H ; intros ;subst ; clear H.
      reflexivity.
  + auto.
Qed.


(** *** Utilities on "getters" *)

(* not used *)
Remark getColumnsReferenceOnLinks_app :
        forall a b c,
         getColumnReferenceOnLinks c (a++b) = 
           match getColumnReferenceOnLinks c a with 
             Some r => Some r 
           | None => getColumnReferenceOnLinks c b end.
Proof.
  induction a ; simpl ; intros b c.
  + reflexivity.
  + destruct a.
  - auto.
  - destruct c0.
    destruct (beq_Column cr c).
    * reflexivity.
    * auto.
Qed.

(* not used *)
Remark getAttributeType_In_back att t (m:Model ClassMM): 
  In (AttributeTypeLink {| source_attribute := att ; a_type := t |}) m.(modelLinks) ->
  getAttributeType att m <> None.
Proof.
  destruct m. simpl.
  unfold getAttributeType ; simpl.
  clear modelElements.
  induction modelLinks ; simpl ; [ congruence | ] ; intro.
  destruct a.
  + (* ClassAttibute *)
    destruct_or H ; [discriminate|].
    apply IHmodelLinks in H ; clear IHmodelLinks.
    exact H.
  + (* AttributeType *)
    destruct a.
    destruct_or H.
  - injection H ; intros ;  clear H ; subst. simpl.
    rewrite beq_Attribute_refl.
    congruence.

  - apply IHmodelLinks in H.
    
    match goal with [ |- context[ if ?P then _ else _ ]  ] => destruct P eqn:? end .
    congruence.
    assumption.
Qed. 

(* FIXME : move-me *)
Ltac duplicate H1 H2 := remember H1 as H2 eqn: TMP ; clear TMP.

Lemma get_in l t v : 
  getAttributeTypeOnLinks v l = return t ->
  exists a,
    In (AttributeTypeLink a) l /\ a.(source_attribute) = v.
Proof.
  induction l ; simpl ; intro G ; [ discriminate | ].
  destruct a.
  { (*ClassAttributeLink*)
    apply IHl in G ; clear IHl.
    destruct G as (a & (IN_E & E)).
    exists a.
    split ; auto.
  }
  { (*AttributeTypeLink*)
    match type of G with (if ?E then _ else _) = _ => destruct E eqn : B  end.
    { (* true *)
      Tactics.inj G.
      exists a.
      split.
      left ; reflexivity.
      apply lem_beq_Attribute_id.
      exact B.
    }
    {
      (* false *)
      clear B.
      apply IHl in G ; clear IHl.
      destruct G as (aa & (IN_E & E)).
      exists aa.
      split ; auto.
    }
  }
Qed.

Lemma in_get_2 :
  forall l v (x:Table_t), 
      In (ColumnReferenceLink {| cr := v ;  ct := x |}) l -> 
      exists r' : Table_t,
        getColumnReferenceOnLinks v l = return r'.
Proof.
  induction l ; simpl ; intros v x IN ; [ contradict IN | ].
  destruct_or IN.
  {
    subst a.
    rewrite lem_beq_Column_refl.
    eauto.
  }
  {
    apply (IHl v) in IN ; auto ; clear IHl ; [].
    destruct IN as [r G].
    rewrite G.
    destruct a ; eauto ; [].
    destruct c.
    destruct ( beq_Column cr v) ; eauto.
  }
Qed.

(* FIXME : not used anymore. *)
Lemma getAttributeType_In att m: 
  getAttributeType att m <> None ->
  exists t, 
    In (AttributeTypeLink {| source_attribute := att ; a_type := t |}) m.(modelLinks).
Proof.
  unfold getAttributeType.
  generalize (modelLinks m). clear.  
  intros l H.
  destruct (getAttributeTypeOnLinks att l) eqn:G ; [ clear H | contradiction ].
  apply get_in in G.
  destruct G as (a & (G1 & G2)).
  destruct att.
  destruct a.
  simpl in *.
  subst.
  eauto.
Qed. 


  
(** *** Result *)

From transformations.Class2Relational Require TraceUtils.

Theorem Relational_Column_Reference_definedness:
forall (cm : ClassModel) (rm : RelationalModel), 

  (* transformation *) rm = execute Class2Relational cm ->

  (* precondition *)  (forall (att : Attribute_t),
    In (AttributeElement att) cm.(modelElements) ->
        exists (r:Class_t), getAttributeType att cm = Some r /\ In (ClassElement r) cm.(modelElements) (*well formed*) ) ->  

  (* postcondition *)  (forall (col: Column_t),
    In (ColumnElement col) rm.(modelElements) ->
      exists r', getColumnReference col rm =Some r'). 

Proof.
  intros cm rm E PRE col I1.
  subst rm.
  Tactics.destruct_execute.
  Tactics.show_singleton.
  Tactics.show_origin.
  repeat Tactics.destruct_any.

  clear IN_I. 
  
  apply Tactics.allModelElements_allTuples_back in IN_E.
  
  specialize (PRE _ IN_E).
  destruct PRE as (t & (PRE1 & PRE2)).
 
  unfold getColumnReference.

  unfold execute.  simpl. 
  unfold getAttributeType in IN_E.

  set (z:=r).

  Tactics.destruct_In_two ; [ exfalso | ] ; 
   simpl in IN_OP ; remove_or_false IN_OP ; subst ope ; [ discriminate I1 | Tactics.inj I1]. 
  
  clear n.
  simpl in M.
  
  Tactics.deduce_element_kind_from_guard. 
 
  destruct a0 ; simpl in *.
  subst derived ; simpl in *. 

  duplicate PRE1 G1.
  apply get_in in PRE1.
  destruct PRE1 as (v & (IN & E)).

  eapply in_get_2 with (x:= {| table_id :=t.(class_id) ;  table_name := t.(class_name) |}) . 
  { 
    apply in_flat_map.
    exists ([AttributeElement {|
                attr_id := attr_id;
                derived := false;
                attr_name := attr_name
              |}]).
    split.
    {
      apply Tactics.allModelElements_allTuples. exact IN_E.
    }
    {

      unfold applyPattern.
    apply in_flat_map.
    exists z.
  
    split.
    { subst z. simpl. auto. }
    { 
      apply tr_applyRuleOnPattern_in ; simpl.
      exists 0.
      split ; [ solve [auto] | ].
      apply tr_applyIterationOnPattern_in.
      eexists  ; split ; [ solve [subst z ; simpl ; auto] | ].
      erewrite tr_applyElementOnPattern_leaf ; simpl.
      2:{ compute. reflexivity. }

      rewrite <- app_nil_end. 
      simpl.
      
      unfold Parser.parseOutputPatternElement ; simpl.
      unfold Parser.parseOutputPatternLink ; simpl.
      unfold ConcreteExpressions.makeLink ; simpl.
      unfold ConcreteExpressions.wrapLink ; simpl.
      unfold getAttributeTypeElement.
      rewrite G1. simpl.


(* on est dans la partie LINK de la seconde règle.*)
(* les LINK sont calculés une fois que tous les éléments ont été construits. *)
(* on voit ca dans la trace *)
      unfold ModelingSemantics.maybeResolve.
      unfold singleton.
      rewrite TraceUtils.in_maybeResolve_trace ; [ | assumption ].

      simpl. left. reflexivity. 
    }
    }
  }
Qed.
     



(* demonstrate how to use instaniate in eexist s*)
Goal exists x, 1 + x = 3.
Proof.                        (* ⊢ exists x, 1 + x = 3 *)
  eexists.                    (* ⊢ 1 + ?42 = 3 *) (* or eapply ex_intro *) 
  simpl.                      (* ⊢ S ?42 = 3 *)
  apply f_equal.              (* ⊢ ?42 = 2 *)
  instantiate (1:=2).         (* place the 1st hold with [2] *)
  reflexivity.                (* proof completed *)
Qed.
