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

Lemma getColumnsReferenceOnLinks_app :
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

Lemma allModelElements_allTuples e (cm:Model ClassMM): 
  In (e) cm.(modelElements) ->
  In [e] (allTuples Class2Relational cm).
Proof. 
  destruct cm ; simpl.
  unfold allTuples ; simpl.
  clear.
  unfold prod_cons.
  induction modelElements ; intro I ; [ solve [inversion I] | ].
  simpl.
  simpl in I.
  destruct_or I ; [ left | right ].
  + subst ; auto. 
  + auto. 
Qed.

Lemma allModelElements_allTuples_back att cm: 
  In [AttributeElement att] (allTuples Class2Relational cm) ->
  In (AttributeElement att) cm.(modelElements).
Proof.
  destruct cm ; simpl.
  unfold allTuples ; simpl.
  clear.
  unfold prod_cons.
  induction modelElements ; simpl ; intro I. 
  + destruct_or I. discriminate. contradiction.
  + destruct_or I ; [ left | right ].
    - inversion_clear I ; auto. 
    - auto.
Qed.

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
  apply allModelElements_allTuples in H.
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
  apply allModelElements_allTuples_back.
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


Lemma getAttributeType_In att m: 
  getAttributeType att m <> None ->
  exists t, 
    In (AttributeTypeLink {| source_attribute := att ; a_type := t |}) m.(modelLinks).
Proof.
  destruct m. simpl.
  unfold getAttributeType ; simpl.
  clear modelElements.
  induction modelLinks ; simpl ; [ congruence | ] ; intro.
  destruct a.
  + (* ClassAttibute *)
    apply IHmodelLinks in H ; clear IHmodelLinks.
    destruct H.
    eexists ; right ; exact H.
  + (* AttributeType *)
    destruct a.
    match goal with [ H : context[ if ?P then _ else _ ] |-_ ] => destruct P eqn:? end.
    -  clear H.
       apply lem_beq_Attribute_id in Heqb ; subst.
       eexists ; left ; reflexivity. 
    - apply IHmodelLinks in H ; clear IHmodelLinks.
      destruct H.
      eexists ; right ; exact H.
Qed.

Lemma getAttributeType_In_back att t (m:Model ClassMM): 
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
    replace (beq_Attribute att att) with true.
    congruence.
    { clear. destruct att ; unfold beq_Attribute ; simpl.
      rewrite Nat.eqb_refl ; simpl.
      rewrite Bool.eqb_reflx ; simpl.
      rewrite lem_beq_string_id.
      reflexivity.
    }

  - apply IHmodelLinks in H.
    
    
    match goal with [ |- context[ if ?P then _ else _ ]  ] => destruct P eqn:? end .
    congruence.
    assumption.
Qed.

Ltac duplicate H1 H2 := remember H1 as H2 eqn: TMP ; clear TMP.

Lemma truc l t v : 
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

Lemma truc2 :
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

Inductive Coherent : TraceLink.TraceLink -> Prop :=
| cons1 :
  forall t,
    Coherent (TraceLink.buildTraceLink 
                ( [ClassElement t], 0, "tab"%string)
                (TableElement
                   {|
                     table_id := class_id t; table_name := class_name t
                   |}))
| cons2 :
  forall a,
  Coherent
    (TraceLink.buildTraceLink ([AttributeElement a], 0, "col"%string)
       (ColumnElement
          {|
            column_id := attr_id a ;
            column_name :=  attr_name a 
          |})).

Lemma wf cm :
  Forall Coherent (trace Class2Relational cm).
Proof.
  unfold trace.
  unfold allTuples.
  apply Forall_flat_map.
  simpl.
  unfold prod_cons.
  apply Forall_forall.
  intro l.
  intro H.
  apply Forall_flat_map.
  apply Forall_forall.
  intro r.
  intro H2.
  apply in_app_or in H.
  destruct_or H.
  2:{ simpl in *.
      remove_or_false H.
      subst l.
      simpl in *.
      contradiction.
  }
  apply in_flat_map in H.
  destruct H as (e & H3 & H4).
  simpl in *.
  remove_or_false H4.
  subst l.
  simpl in *.
  unfold matchPattern in H2.
  apply filter_In in H2.
  destruct H2 as [H4 H5].

  
  Tactics.destruct_In_two ; simpl in * ; Tactics.deduce_element_kind_from_guard.
  { repeat constructor. }  
  { repeat constructor. }  
Qed.



Lemma truc5bis l : 
  Forall Coherent l ->
  forall t,
    In (TraceLink.buildTraceLink
          ([ClassElement t], 0, "tab"%string)
          (TableElement {| table_id := class_id t; table_name := class_name t |})) l ->
    exists r1 , 
      find
        (fun tl : TraceLink.TraceLink =>
           (Semantics.list_beq
              (Metamodel.ElementType
                 TransformationConfiguration.SourceMetamodel)
              TransformationConfiguration.SourceElement_eqb
              (TraceLink.TraceLink_getSourcePattern tl)
              (singleton (ClassElement t)) &&
              (TraceLink.TraceLink_getIterator tl =? 0) &&
              (TraceLink.TraceLink_getName tl =? "tab")%string)%bool) l = 
        Some (TraceLink.buildTraceLink r1 (TableElement {| table_id := class_id t; table_name := class_name t |})).
Proof.
  induction l ; intros C t IN1 ; [ simpl in IN1 ; contradict IN1 | ].
  simpl.
  apply in_inv in IN1. 
  compare a (TraceLink.buildTraceLink ([ClassElement t], 0, "tab"%string)
          (TableElement
             {| table_id := class_id t; table_name := class_name t |})). 


  { (* case where the class/table is the first element of the list : no induction *)
    clear IN1 ; intro ; subst a.
    simpl.
    unfold TransformationConfiguration.SourceElement_eqb .
    unfold Metamodel.elements_eqdec.
    unfold TransformationConfiguration.SourceMetamodel.
    unfold C2RConfiguration. simpl.
    rewrite beq_Class_refl. simpl.
    eauto.
  }           
  
  { (* case where the class/table is not the first element of the list. *)
    intro D.
    inversion_clear C ; subst.
    
    inversion_clear H.
    { (* class/table *)
      destruct_or IN1 ; [ contradict D ; assumption | ].

      destruct (IHl H0 t) ; [  exact IN1 | ].
      unfold TransformationConfiguration.SourceElement_eqb .
      unfold Metamodel.elements_eqdec.
      unfold TransformationConfiguration.SourceMetamodel.
      unfold C2RConfiguration. simpl.
      repeat rewrite Bool.andb_true_r.
      destruct (beq_Class t0 t) eqn:BEQ.
      {  apply lem_beq_Class_id in BEQ ; subst ; eauto.  }
      {
        simpl in H.

        unfold TransformationConfiguration.SourceElement_eqb in H.
        unfold Metamodel.elements_eqdec.
        
        match goal with 
          [ H : find ?X ?Y = ?Z |- context [find ?A ?B] ] => 
            replace (find A B) with Z end.
        { eauto. }
      }
    }       
    { (* attribute/column*)
      destruct_or IN1.
      { contradict IN1. exact D. }
      destruct (IHl H0 t) ; [  exact IN1 | ].
      unfold TransformationConfiguration.SourceElement_eqb .
      unfold Metamodel.elements_eqdec.
      unfold TransformationConfiguration.SourceMetamodel.
      unfold C2RConfiguration. simpl. 
      exists x.
      apply H.
    }
  }
  { repeat decide equality. }
  { repeat decide equality. }

Qed.            
        

      
Lemma truc4bis  l t cm : 
  Forall Coherent l ->
  In (TraceLink.buildTraceLink
        ([ClassElement t], 0, "tab"%string)
        (TableElement
           {| table_id := class_id t; table_name := class_name t |})) l ->
  resolveIter l cm "tab"
    (singleton (ClassElement t)) 0 = Some (TableElement {| table_id := class_id t; table_name := class_name t |}).
Proof.
  unfold resolveIter. 
  intros C IN1.
  specialize (truc5bis l C t IN1) ; intro T5 ; clear IN1.
  
  destruct T5 as (t1 & IN1).
  rewrite IN1.
  unfold TraceLink.TraceLink_getTargetElement.
  destruct t1.
  destruct p.
  reflexivity.
Qed.

Lemma truc3  e (cm : ClassModel) : 
  In (ClassElement e) cm.(modelElements) -> 
  In 
    (TraceLink.buildTraceLink ([ClassElement e],0,"tab"%string) (TableElement {| table_id := class_id e; table_name := class_name e |})) 
    (trace Class2Relational cm).
Proof.
  intro IN1.
  unfold trace.
  apply in_flat_map.
  exists ([ClassElement e]).
  split.
  { apply allModelElements_allTuples ; auto. } 
  
  simpl.
  left.
  reflexivity.
Qed.

  
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
  
  apply allModelElements_allTuples_back in IN_E.
  
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
  apply truc in PRE1.
  destruct PRE1 as (v & (IN & E)).

  eapply truc2 with (x:= {| table_id :=t.(class_id) ;  table_name := t.(class_name) |}) . 
  { 
    apply in_flat_map.
    exists ([AttributeElement {|
                attr_id := attr_id;
                derived := false;
                attr_name := attr_name
              |}]).
    split.
    {
      apply allModelElements_allTuples. exact IN_E.
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
      2:{
        unfold ConcreteExpressions.makeElement. 
        unfold ConcreteExpressions.wrapElement. simpl.
        reflexivity.
      }

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
      unfold maybeResolve ; simpl.
      unfold resolve. 

      apply truc3 in PRE2.

    specialize (truc4bis (trace Class2Relational cm) t cm ) ; 
        intro T4.
      specialize (T4 (wf _) PRE2). 
      
      match goal with
        [ |- context [ModelingSemantics.denoteOutput _ ?A ] ] => 
          replace A with (Some (TableElement {| table_id := class_id t ; table_name := class_name t |})) end.
      simpl.
      left.
      reflexivity.
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
