Require Import String.

Require Import Lia.
Require Import Nat.
Require Import EqNat.
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Engine.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Resolve.
Require Import core.Metamodel.
Require Import core.TransformationConfiguration.
Require Import core.SyntaxCertification.
Require Import core.EvalUserExpressions.


Section Certification.

Context {tc : TransformationConfiguration}.

Lemma tr_execute_in_elements :
forall (tr: Transformation) (sm : SourceModel) (te : TargetElementType),
  In te (execute tr sm).(modelElements) <->
  (exists (sp : list SourceElementType),
      In sp (allTuples tr sm) /\
      In te (instantiateTrOnPiece tr sm sp)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_execute_in_links :
forall (tr: Transformation) (sm : SourceModel) (tl : TargetLinkType),
  In tl (execute tr sm).(modelLinks) <->
  (exists (sp : list SourceElementType),
      In sp (allTuples tr sm) /\
      In tl (applyTrOnPiece tr sm sp)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_matchingRules_in :
forall (tr: Transformation) (sm : SourceModel),
  forall (sp : list SourceElementType)(r : Rule),
    In r (matchingRules tr sm sp) <->
      In r tr.(rules) /\
      EvalUserExpressions.evalGuard r sm sp = true.
Proof.
  intros.
  apply filter_In.
Qed.


Lemma tr_instantiateOnPiece_in :
forall (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) (te : TargetElementType),
  In te (instantiateTrOnPiece tr sm sp) <->
  (exists (r : Rule),
      In r (matchingRules tr sm sp) /\
      In te (instantiateRuleOnPiece r sm sp)).
Proof.
  intros.
  unfold instantiateTrOnPiece, instantiateRuleOnPiece.
  unfold traceTrOnPiece.
  rewrite map_flat_map.
  apply in_flat_map.
Qed.

Lemma tr_instantiateRuleOnPiece_in :
forall (r : Rule) (sm : SourceModel) (sp: list SourceElementType) (te : TargetElementType),
  In te (instantiateRuleOnPiece r sm sp) <->
  (exists (i: nat),
      In i (seq 0 (evalIterator r sm sp)) /\
      In te (map produced (traceIterationOnPiece r sm sp i))).
Proof.
  intros.
  unfold instantiateRuleOnPiece.
  unfold traceRuleOnPiece.
  rewrite map_flat_map.
  apply in_flat_map.
Qed.

Lemma tr_instantiateIterationOnPiece_in : 
forall (r : Rule) (sm : SourceModel) (sp: list SourceElementType) (te : TargetElementType) (i:nat),
  In te (map produced (traceIterationOnPiece r sm sp i))
  <->
  (exists (opu: OutputPatternUnit),
      In opu r.(r_outputPattern) /\ 
       option_map produced (traceElementOnPiece opu sm sp i) = Some te).
Proof.
  unfold traceIterationOnPiece.
  intros r sm sp te i.
  rewrite map_flat_map.
  split ; intros.
  * apply in_flat_map in H.
    destruct H as (x, (H, H0)).
    exists x.
    unfold optionToList in H0.
    split. 
    - exact H.
    - destruct (traceElementOnPiece x sm sp i).
      ** crush.
      ** contradiction.
  * apply in_flat_map.
    destruct H as (x, (H, H0)).
    exists x.
    split.
    - exact H.
    - monadInv H0.
      crush.
Qed.

Lemma  tr_instantiateElementOnPiece_leaf:
      forall (o: OutputPatternUnit) (sm: SourceModel) (sp: list SourceElementType) (iter: nat),
        option_map produced (traceElementOnPiece o sm sp iter) = evalOutputPatternElement o sm sp iter.
Proof.
  intros.
  unfold traceElementOnPiece.
  destruct (evalOutputPatternElement o sm sp iter) ; reflexivity.
Qed.

Lemma tr_applyOnPiece_in :
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) (tl : TargetLinkType),
      In tl (applyTrOnPiece tr sm sp) <->
      (exists (r : Rule),
          In r (matchingRules tr sm sp) /\
          In tl (applyRuleOnPiece r tr sm sp)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyRuleOnPiece_in : 
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceElementType) (tl : TargetLinkType),
      In tl (applyRuleOnPiece r tr sm sp) <->
      (exists (i: nat),
          In i (seq 0 (evalIterator r sm sp)) /\
          In tl (applyIterationOnPiece r tr sm sp i)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyIterationOnPiece_in : 
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceElementType) (tl : TargetLinkType) (i:nat),
      In tl (applyIterationOnPiece r tr sm sp i) <->
      (exists (opu: OutputPatternUnit),
          In opu r.(r_outputPattern) /\ 
          In tl (applyUnitOnPiece opu tr sm sp i)).
Proof.
  intros.
  apply in_flat_map.
Qed.

Lemma tr_applyUnitOnPiece_leaf : 
forall (tr: Transformation) (sm : SourceModel) (sp: list SourceElementType) (te: TargetElementType) 
       (i:nat) (opu: OutputPatternUnit),
  evalOutputPatternElement opu sm sp i = Some te ->
  applyUnitOnPiece opu tr sm sp i = optionListToList (evalOutputPatternLink sm sp te i (traceTrOnModel tr sm) opu).
Proof.
  intros.
  destruct (evalOutputPatternLink sm sp te i (traceTrOnModel tr sm) opu) eqn:dst.
  * unfold applyUnitOnPiece. crush.
  * unfold applyUnitOnPiece. crush.
Qed.  

(*TODO
Lemma maxArity_length:
  forall (sp : list SourceElementType) (tr: Transformation) (sm: SourceModel), 
  gt (length sp) (maxArity tr) -> In sp (allTuples tr sm) -> False.
*)


Lemma allTuples_incl:
  forall (sp : list SourceElementType) (tr: Transformation) (sm: SourceModel), 
  In sp (allTuples tr sm) -> incl sp sm.(modelElements).
Proof.
  intros.
  unfold allTuples in H. simpl in H. 
  apply tuples_up_to_n_incl in H.
  assumption.
Qed.

Lemma allTuples_incl_length:
  forall (sp : list SourceElementType) (tr: Transformation) (sm: SourceModel), 
  incl sp sm.(modelElements) -> 
  length sp <= tr.(arity) ->
  In sp (allTuples tr sm).
Proof.
  intros.
  unfold allTuples.
  apply tuples_up_to_n_incl_length with (n:=tr.(arity)) in H.
  - assumption.
  - assumption.
Qed.


Lemma allTuples_not_incl_length:
  forall (sp : list SourceElementType) (tr: Transformation) (sm: SourceModel), 
  length sp > tr.(arity) -> not (In sp (allTuples tr sm)).
Proof.
intros sp tr sm c.
apply Gt.gt_not_le in c.
revert c.
apply contraposition.
unfold allTuples.
specialize (tuple_length sp sm.(modelElements) tr.(arity)).
crush.
Qed.

(** * Resolve *)

Theorem tr_resolveAll_in:
  forall (tls: list TraceLink) (sm: SourceModel) (name: string)
    (sps: list(list SourceElementType)),
    resolveAll tls sm name sps = resolveAllIter tls sm name sps 0.
Proof.
  crush.
Qed.

Theorem tr_resolveAllIter_in:
  forall (tls: list TraceLink) (sm: SourceModel) (name: string)
          (sps: list(list SourceElementType)) (iter: nat)
    (te: TargetElementType),
    (exists tes: list TargetElementType,
        resolveAllIter tls sm name sps iter = Some tes /\ In te tes) <->
    (exists (sp: list SourceElementType),
        In sp sps /\
        resolveIter tls sm name sp iter = Some te).
Proof.
  intros.
      intros.
  split.
  - intros.
    destruct H. destruct H.
    unfold resolveAllIter in H.
    inversion H.
    rewrite <- H2 in H0.
    apply in_flat_map in H0.
    destruct H0. destruct H0.
    exists x0. split; auto.
    destruct (resolveIter tls sm name x0 iter).
    -- unfold optionToList in H1. crush.
    -- crush.
  - intros.
    destruct H. destruct H.
    remember (resolveAllIter tls sm name sps iter) as tes1.
    destruct tes1 eqn: resolveAll.
    -- exists l.
        split. auto.
        unfold resolveAllIter in Heqtes1.
        inversion Heqtes1.
        apply in_flat_map.
        exists x. split. auto.
        destruct (resolveIter tls sm name x iter).
        --- crush.
        --- crush.
    -- unfold resolveAllIter in Heqtes1.
        crush.
Qed.

(* this one direction, the other one is not true since exists cannot gurantee uniqueness in find *)
Theorem tr_resolveIter_leaf: 
  forall (tls:list TraceLink) (sm : SourceModel) (name: string)
    (sp: list SourceElementType) (iter: nat) (x: TargetElementType),
    resolveIter tls sm name sp iter = return x ->
      (exists (tl : TraceLink),
        In tl tls /\
        Is_true (list_beq _ (@elements_eqdec tc.(SourceMetamodel)) (TraceLink.getSourcePattern tl) sp) /\
        ((TraceLink.getIteration tl) = iter) /\ 
        ((TraceLink.getName tl) = name)%string /\
        tl.(produced) = x).
Proof.
intros.
unfold resolveIter in H.
match type of H with context[find ?F tls] => destruct (find F tls) eqn: find_ca end.
- exists t.
  apply find_some in find_ca.
  destruct find_ca.
  symmetry in H1.
  apply andb_true_eq in H1.
  destruct H1.
  apply andb_true_eq in H1.
  destruct H1.
  crush.
  -- apply beq_nat_true. crush.
  -- apply String.eqb_eq. crush.
- inversion H.
Qed.


Instance CoqTLEngine :
  TransformationEngine CoqTLSyntax :=
  {

    (* semantic functions *)

    execute := execute;

    matchPattern := matchingRules;
    matchRuleOnPattern := evalGuardExpr ;

    instantiatePattern := instantiateTrOnPiece;
    instantiateRuleOnPattern := instantiateRuleOnPiece;
    instantiateIterationOnPattern := fun  r sm sp iter => map produced (traceIterationOnPiece r sm sp iter) (*instantiateIterationOnPiece*) ;
    instantiateElementOnPattern := fun opu sm ip it => option_map produced (traceElementOnPiece opu sm ip it) (*instantiateElementOnPiece*) ;

    applyPattern := applyTrOnPiece;
    applyRuleOnPattern := applyRuleOnPiece;
    applyIterationOnPattern := applyIterationOnPiece;
    applyElementOnPattern := applyUnitOnPiece;

    trace := traceTrOnModel ;

    resolveAll := resolveAllIter;
    resolve := resolveIter;

    (* lemmas *)

    tr_execute_in_elements := tr_execute_in_elements;
    tr_execute_in_links := tr_execute_in_links;

    tr_matchPattern_in := tr_matchingRules_in;
    tr_matchRuleOnPattern_leaf := fun _ _ _ _ => eq_refl ;

    tr_instantiatePattern_in := tr_instantiateOnPiece_in;
    tr_instantiateRuleOnPattern_in := tr_instantiateRuleOnPiece_in;
    tr_instantiateIterationOnPattern_in := tr_instantiateIterationOnPiece_in;
    tr_instantiateElementOnPattern_leaf := tr_instantiateElementOnPiece_leaf;

    tr_applyPattern_in := tr_applyOnPiece_in;
    tr_applyRuleOnPattern_in := tr_applyRuleOnPiece_in;
    tr_applyIterationOnPattern_in := tr_applyIterationOnPiece_in;
    tr_applyElementOnPattern_leaf := tr_applyUnitOnPiece_leaf;

    tr_resolveAll_in := tr_resolveAllIter_in;
    tr_resolve_leaf := tr_resolveIter_leaf;

    allTuples_incl := allTuples_incl;
    (*tr_matchPattern_None := tr_matchingRules_None;

    tr_matchRuleOnPattern_None := tr_matchRuleOnPiece_None;

    tr_instantiatePattern_non_None := tr_instantiateOnPiece_non_None;
    tr_instantiatePattern_None := tr_instantiateOnPiece_None;

    tr_instantiateRuleOnPattern_non_None := tr_instantiateRuleOnPiece_non_None;

    tr_instantiateIterationOnPattern_non_None := tr_instantiateIterationOnPiece_non_None;

    tr_instantiateElementOnPattern_None := tr_instantiateElementOnPiece_None;
    tr_instantiateElementOnPattern_None_iterator := tr_instantiateElementOnPiece_None_iterator;

    tr_applyPattern_non_None := tr_applyOnPiece_non_None;
    tr_applyPattern_None := tr_applyOnPiece_None;

    tr_applyRuleOnPattern_non_None := tr_applyRuleOnPiece_non_None;

    tr_applyIterationOnPattern_non_None := tr_applyIterationOnPiece_non_None;

    tr_applyElementOnPattern_non_None := tr_applyUnitOnPiece_non_None;

    tr_applyLinkOnPattern_None := tr_applyLinkOnPiece_None;
    tr_applyLinkOnPattern_None_iterator := tr_applyLinkOnPiece_None_iterator;

    tr_maxArity_in := tr_maxArity_in;

    tr_instantiateElementOnPattern_Leaf := tr_instantiateElementOnPiece_Leaf;
    tr_applyLinkOnPattern_Leaf := tr_applyLinkOnPiece_Leaf;
    tr_matchRuleOnPattern_Leaf := tr_matchRuleOnPiece_Leaf;

    tr_resolveAll_in := tr_resolveAllIter_in;
    tr_resolve_Leaf := tr_resolveIter_Leaf';*)
  }. 



(* matched sp must produce matched rule's output element 
  genearlization of lemma such as: Attribute_name_preservation
*)

Lemma tr_match_injective :
  forall (sm : SourceModel)(sp : list SourceElementType)(r : Rule)(iter: nat),
    In iter (seq 0 (evalIterator r sm sp)) /\ 
      (exists opu, In opu r.(r_outputPattern) /\  (evalOutputPatternElement opu sm sp iter) <> None ) ->
    (exists (te: TargetElementType),  In te (instantiateRuleOnPiece r sm sp) ).
Proof.
  intros.
  destruct H as [Hiter Hopu].
  destruct Hopu as [opu HopuIn].
  destruct HopuIn as [HopuInr HopuEval].
  apply option_res_dec in HopuEval.
  destruct HopuEval as [te Hte].
  exists te.
  unfold instantiateRuleOnPiece.
  unfold traceRuleOnPiece.
  rewrite map_flat_map.
  apply in_flat_map.
  exists iter.
  split.
  - exact Hiter.
  - unfold traceIterationOnPiece.
    rewrite map_flat_map.
    apply in_flat_map.
    exists opu. 
    split. 
    -- exact HopuInr.
    -- unfold traceElementOnPiece.
       rewrite Hte. 
       crush.
Qed.

(*Theorem tr_instantiateRuleAndIterationOnPiece_in' :
forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceElementType) (te : TargetElementType),
  In te (instantiateRuleOnPiece r sm sp) <->
  (exists (i: nat),
      In i (seq 0 (evalIteratorExpr r sm sp)) /\
      (exists (opu: OutputPatternUnit),
      In opu (Rule_getOutputPatternElements r) /\ 
        instantiateElementOnPiece opu sm sp i = Some te)).
Proof.
  intros.
  specialize (tr_instantiateRuleOnPiece_in tr r sm sp te) as inst. 
  rewrite tr_instantiateIterationOnPiece_in with (r:=r) (sp:=sp) (te:=te) (sm:=sm)  in inst.
  assumption. *)

End Certification.
