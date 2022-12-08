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


Lemma allModelElements_allTuples att (cm:Model ClassMM): 
  In (AttributeElement att) cm.(modelElements) ->
  In [AttributeElement att] (allTuples Class2Relational cm).
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
    - destruct_or H ; [ | contradiction].
      injection H ; intros ;subst ; clear H.
      reflexivity.
  + auto.
Qed.

(* nul
Lemma apply_pattern_attribute id name cm :  
  applyPattern Class2Relational cm
    [AttributeElement
       {|
         attr_id := id;
         derived := false;
         attr_name := name
       |}] = nil .
Proof.
  destruct cm.

  unfold applyPattern. 
  simpl.
  rewrite <- List.app_nil_end.
  simpl flat_map.


, Class2Relational ; simpl.
  unfold Parser.parse, Class2Relational' ; simpl.
  unfold Parser.parseRule ; simpl.
  unfold applyRuleOnPattern ; simpl.
  compute.
Qed. *)

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


Theorem Relational_Column_Reference_definedness:
forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  (forall (att : Attribute_t),
    In (AttributeElement att) cm.(modelElements) ->
        getAttributeType att cm <> None) ->
  (* postcondition *)  (forall (col: Column_t),
    In (ColumnElement col) rm.(modelElements) ->
      getColumnReference col rm <> None). 
Proof.
  intros cm rm E PRE col I1.
  subst rm.

Ltac duplicate H1 H2 := remember H1 as H2 eqn: TMP ; clear TMP.

{

  duplicate I1 I2.
  destruct col. 
  eapply transform_attribute_back in I2 ; [ | reflexivity ].
  rename column_id into i.
  rename column_name into n.

  duplicate I2 I3.
  
  apply PRE in I3 ; clear PRE.
  destruct cm ; simpl in *.


  duplicate I3 I4. 
  apply getAttributeType_In_back in I4.
  {
    clear I1 I2.
    unfold getAttributeType in I3.


  Tactics.destruct_execute.  
  Tactics.show_singleton.
  Tactics.show_origin.
  repeat Tactics.destruct_any.

  unfold getAttributeType in I.
  destruct cm.
  unfold getColumnReference ; simpl.

}*)
Tactics.destruct_execute.
  Tactics.show_singleton.
  Tactics.show_origin.
  repeat Tactics.destruct_any.
  rename x into r. 
  rename x0 into n.
  rename H0 into Hn.
  match goal with 
    [ H : context[match ?P with _ => _ end] |- _ ] => destruct P eqn:E 
  end ; [ | discriminate ].
  destruct b ; [ clear H1 | discriminate ].


  unfold getColumnReference.
  unfold execute ; simpl.

  rename H into Hr.
  rename H2 into Hop.
  rename H3 into He. 
  unfold Expressions.evalOutputPatternElementExpr in He.


  cut (In (AttributeElement a) (allModelElements cm)).
  {
    intro IA.
    specialize (PRE a IA) ; clear IA.
    

  Tactics.destruct_In_two ; simpl in *.
  {
    (* first rule *)
    exfalso.
    destruct Hop as [Hop | Hop] ; [ | contradiction].
    destruct Hn ; [ | contradiction ] ; subst n.
    subst ope.
    simpl in He.
    unfold Expressions.evalExpr in He.
    unfold ConcreteExpressions.makeElement in He.
    simpl in He.
    discriminate.
  }
  {
    (* second rule *)
    destruct Hop as [Hop | Hop] ; [ | contradiction].        
    subst ope.
    simpl in He.
    destruct Hn ; [ | contradiction ] ; subst n.
    unfold ConcreteExpressions.makeElement in He.
    simpl in He.
    unfold Expressions.evalExpr in He.
    simpl in He.
    injection He ; intro ; clear He ; subst col.
    simpl in *.
    unfold ConcreteExpressions.makeGuard in E ; simpl in E.
    injection E ; intro D ; clear E. 
    
    contradict PRE.
(*    Set Printing All. *)

    replace (@allTuples
           (@tc ClassMetamodel.Object ClassMetamodel.Link ClassMetamodel.EqDec
              Object Link EqDec) Class2Relational cm) with (@allTuples C2RConfiguration Class2Relational cm) in I.
    { 
      revert PRE.
      revert I.

    generalize (allTuples Class2Relational cm).
    induction l ; [ contradiction  | ]; simpl ; intros .
    destruct I as [ I | I].
    {
      subst.
      rewrite getColumnsReferenceOnLinks_app in PRE.
      match goal with [H:context [ match ?P with | _ => _ end] |- _] => destruct P eqn:? end.
      discriminate.
      clear IHl.
      destruct a.
      destruct derived ; [ discriminate | ].
      simpl in *.

      unfold applyPattern in Heqo.
      compute in Heqo. simpl in Heqo.
    }

Qed.
(* *)*)
intros cm rm tr pre.
intros. 
rewrite tr.

assert 
(exists t: Table, 
  In (ColumnReferenceLink 
        (Build_ColumnReference col t))
     (allModelLinks rm)) as HcolInrml.
{  
eexists.
rewrite tr.
apply tr_execute_in_links.

(* get the sp that corresponds to [col] *)

rewrite tr in H.
apply tr_execute_in_elements in H.
destruct H as [sp H].
destruct H as [HspIncm HcolInInst].
remember HspIncm as HspIncm_copy.
clear HeqHspIncm_copy.
destruct sp as [ | sphd sptl] eqn: sp_ca. (* Case analysis on source pattern *)
- (* Empty pattern *) contradiction HcolInInst.
- destruct sptl eqn: sptl_ca.
  + (* Singleton *) 
    apply allTuples_incl in HspIncm.
    unfold incl in HspIncm.
    specialize (HspIncm sphd).
    assert (In sphd [sphd]). { left. reflexivity. }
    specialize (HspIncm H).  
    destruct sphd as [ sphd_elem | sphd_elem]. (*as [sphd_tp sphd_elem]. 
    destruct sphd_tp*) (* Case analysis on source element type *)
    ++ (* [Class] *) simpl in HcolInInst.
      destruct HcolInInst.
      +++ inversion H0. (* contradiction in H0 *)
      +++ crush.
    ++ (* [Attribute] *) destruct sphd_elem as [attr_id attr_der attr_name] eqn: sphd_elem_attr.
      destruct attr_der eqn: attr_der_ca. (* Case analysis on attribute derivable *)
      +++ (* derived *) contradiction HcolInInst.
      +++ (* not derived *) 
         exists sp.
         split.
         * rewrite <- sp_ca in HspIncm_copy. exact HspIncm_copy.
         * 
remember (applyPattern Class2Relational cm sp) as Rapply.
rename HeqRapply into Happly.
(*rewrite Happly.*)
rewrite sp_ca.
unfold applyPattern.
unfold applyRuleOnPattern.
unfold applyIterationOnPattern.
unfold applyElementOnPattern.
simpl.
unfold ConcreteExpressions.makeLink.
unfold ConcreteExpressions.wrapOptionLink. 

destruct ( 
(ClassMetamodel.AttributeElement
   (Build_Attribute attr_id false attr_name))) eqn: link_cast_ca.
**  (* <> None *)
    unfold optionToList.
    simpl.
(*    unfold maybeBuildColumnReference.
    unfold ModelingSemantics.maybeResolve.
    unfold ModelingSemantics.denoteOutput.
    unfold maybeResolve'.
    unfold maybeSingleton.
    unfold option_map.*)
    destruct (getAttributeTypeObject d cm) eqn: link_expr_cl_ca.
    *** destruct (resolve' (trace Class2Relational cm) cm "tab"
(singleton c)) eqn: link_expr_tb_ca.
        **** destruct (toModelClass TableClass r) eqn: tb_cast_ca.
             ***** simpl. left. 
                   simpl in HcolInInst.
                   destruct HcolInInst eqn: Hinst_ca.
                   ****** unfold toModelElement  in e.
                          unfold toSumType   in e.
                          simpl in e.
                          unfold toModelLink.
                          unfold toSumType.
                          simpl.
                          clear Hinst_ca.
                          apply rel_invert in e.
                          rewrite e.
                          unfold RelationalMetamodel_toLink.
                          (* instantiate (1:=d0). *)
                          admit.
                   ****** crush.
             ***** admit. (* contradiction in resolve_ca and cast_ca *)
        **** admit. (* contradiction in do_ca and resolve_ca *)
    *** (* contradiction in pre, only if attr in cm_elem *)
        rename d into attr.
        inversion link_cast_ca as [attr_ctr].
        rewrite attr_ctr in HspIncm.
        specialize (pre attr HspIncm).
        unfold getAttributeTypeObject in link_expr_cl_ca.
        apply option_res_dec in pre.
        destruct pre as [class Hclass]. 
        rewrite Hclass in link_expr_cl_ca.
        inversion link_expr_cl_ca.
** (* x0 <> nil contradiction *)
   inversion link_cast_ca. 
  + (* Other patterns *) 
    rename c into sptlhd.
    rename l into sptltl.
    destruct sptlhd as [sptlhd_tp sptlhd_elem].
    destruct sptlhd_tp eqn: sptlhd_tp_ca.
    * destruct sphd. destruct c; contradiction HcolInInst.
    * destruct sphd. destruct c; contradiction HcolInInst.
}

rewrite <- tr.
unfold getColumnReference.

induction (allModelLinks rm) as [nil | hd tl].
- simpl in HcolInrml.
  destruct HcolInrml.
  contradiction.
- destruct hd as [hdtp hdlk].
  destruct hdtp as [tabcolumns | colref].
  -- simpl.
     apply IHtl.
     simpl in HcolInrml.
     crush.
     exists x.
     exact H1.
  -- simpl.
     simpl in HcolInrml.
     destruct HcolInrml as [tab Htab].
     destruct Htab.
     --- destruct hdlk.
         apply rel_elink_invert in H0.
         inversion H0.
         assert (beq_Column col col = true). { admit. }
         rewrite H1.
         apply option_res_dec.
         exists tab.
         reflexivity.
     --- destruct hdlk.
         destruct (beq_Column c col).
         ---- crush.
         ---- apply IHtl.
              exists tab.
              exact H0.

Admitted.


(* demonstrate how to use instaniate in eexist s*)
Goal exists x, 1 + x = 3.
Proof.                        (* ⊢ exists x, 1 + x = 3 *)
  eapply ex_intro.            (* ⊢ 1 + ?42 = 3 *)
  simpl.                      (* ⊢ S ?42 = 3 *)
  apply f_equal.              (* ⊢ ?42 = 2 *)
  instantiate (1:=2).         (* place the 1st hold with [2] *)
  reflexivity.                (* proof completed *)
Qed.
