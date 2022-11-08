(**
 CoqTL user theorem: Relational_name_definedness
 Def: if all objects in the source model have name defined,
      then the target objects generated in the target model
      have name defined. 
 **)

Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.

Require Import core.utils.Utils.
Require Import core.SyntaxCertification.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import core.Engine.

Require Import  core.Semantics.
Require Import  core.Certification.


Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From transformations.Class2Relational Require Tactics.

(*Ltac unfoldTransformationIn Tr Ht := 
  unfold Tr in Ht;
  unfold ConcreteSyntax.parse in Ht; 
  unfold ConcreteSyntax.parseRule in Ht;
  unfold ConcreteSyntax.parseOutputPatternElement in Ht;
  unfold ConcreteSyntax.parseOutputPatternLink in Ht;
  unfold Expressions.makeGuard in Ht;
  unfold Expressions.makeElement in Ht;
  unfold Expressions.makeIterator in Ht;
  unfold Expressions.makeLink in Ht;
  repeat (unfold Expressions.wrapOptionElement in Ht);
  repeat (unfold Expressions.wrapOptionLink in Ht);
  repeat (unfold Expressions.wrapOption in Ht);
  simpl in Ht.

Ltac unfoldTransformation Tr := 
  unfold Tr;
  unfold ConcreteSyntax.parse; 
  unfold ConcreteSyntax.parseRule;
  unfold ConcreteSyntax.parseOutputPatternElement;
  unfold ConcreteSyntax.parseOutputPatternLink;
  unfold Expressions.makeGuard;
  unfold Expressions.makeElement;
  unfold Expressions.makeIterator;
  unfold Expressions.makeLink;
  repeat (unfold Expressions.wrapOptionElement);
  repeat (unfold Expressions.wrapOptionLink);
  repeat (unfold Expressions.wrapOption);
  simpl.*)


Theorem Relational_name_definedness:
forall (te: TransformationEngine CoqTLSyntax) (cm : ClassModel) (rm : RelationalModel),
  (* transformation *) 
     rm = execute Class2Relational cm ->
  (* precondition *)   
     (forall (c1 : ClassMetamodel.Object), 
         In c1 (allModelElements cm) -> 
            (ClassMetamodel.getName c1 <> ""%string)) ->
  (* postcondition *) 
     (forall (t1 : RelationalMetamodel.Object), 
         In t1 (allModelElements rm) -> 
            (RelationalMetamodel.getName t1 <> ""%string)). 
Proof.
  intros.
  subst rm.

  Tactics.destruct_execute.

  Tactics.show_singleton. 

  rename x into c.

  specialize (H0 c). 
  apply allTuples_incl in H1.
  unfold incl in H1.
  specialize (H1 c).
  assert (In c [c]). { left. reflexivity. }
  specialize (H0 (H1 H2)).
  destruct c. (* Case analysis on source element type *)
  * (* [Class] *) 
    repeat Tactics.destruct_any.
    
    Tactics.destruct_In_two. 
    ** (* Class2Table *)
      simpl in H5.
      destruct H5 ; [ | contradiction ] ; subst ope.
      simpl in H6.
      inversion_clear H6.
      simpl. 
      apply H0.
      
    **  (* Attribute2Column contradict *)
      exfalso.
      simpl in H5.
      destruct H5 ; [ | contradiction ].
      subst ope.
      simpl in H6. 
      inversion H6.
      
      
  * (* [Attribute] *) 
    destruct a.
    destruct derived ; repeat Tactics.destruct_any.
    -- (* derived *)
      exfalso.
      Tactics.destruct_In_two. 
      ** simpl in H4 ; inversion H4.
      ** simpl in H4 ; inversion H4.
             
    -- (* not derived *) 
      Tactics.destruct_In_two.
      **  (* Class2Table contradict *)
        exfalso.
        simpl in H5.
        destruct H5 ; [ | contradiction] ; subst ope.
        simpl in H6; inversion H6.
        
      ** (* Attribute2Column *) 
        simpl in H5.
        destruct H5 ; [ | contradiction ].
        subst ope.
        simpl in H6 ; inversion_clear H6.
        simpl. 
        apply H0.
Qed.

(* Alternative for (* [Attribute] *):
      unfold instantiatePattern in H2. 
      unfold matchPattern in H2.
      unfold matchRuleOnPattern in H2. simpl in H2.
      destruct (negb (getAttributeDerived c0)). 
      -- simpl in H2. destruct H2. 
        ++ rewrite <- H2. simpl. simpl in H0. assumption.
        ++ contradiction H2. 
      --  contradiction H2.*)

(* Alternative for (* Other patterns *): 
      apply maxArity_length with (sp:=c::c0::x) (tr:=Class2Relational) (sm:=cm).
      * unfold maxArity. simpl. omega.
      * assumption. *)

(*Ltac destructPattern sp tr sm h := 
  destruct sp;
  [> contradiction | 
     repeat
      destruct sp;
       [> 
          | exfalso;
            apply maxArity_length with (sp:=c::c0::x) (tr:=tr) (sm:=sm);
            [> 
              parseTransformationInGoal tr; unfold maxArity; simpl; omega |
              assumption 
            ]
            +
            destruct sp;
       ]  
  ].*)
  

Ltac destruct_rule Hrule :=
  repeat (destruct Hrule as [Hrule | Hrule]; try contradiction Hrule); destruct Hrule.

Ltac destruct_pattern Hinst sp :=
  repeat (let se := fresh "se" in
          destruct sp as [ | se sp ];
          [ | destruct se as [[] ?] eqn:?];
          try contradiction Hinst);
  destruct Hinst as [Hinst | []]; simpl in Hinst.

(* 

Theorem Relational_name_definedness':
forall (cm : ClassModel) (rm : RelationalModel),
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)   (forall (c1 : ClassMetamodel_Object), In c1 (allModelElements cm) -> (ClassMetamodel_getName c1 <> ""%string)) ->
  (* postcondition *)  (forall (t1 : RelationalMetamodel_Object), In t1 (allModelElements rm) -> (RelationalMetamodel_getName t1 <> ""%string)).
Proof.
  intros. subst rm.
  destruct_execute H1 sp Hin Hinst. (* t1 comes from a pattern sp *)
  apply allTuples_incl in Hin. (* sp is made of source model elements *)
  destruct_instantiatePattern Hinst r Hr Hinst. (* sp matches a rule r *)
  destruct_matchPattern Hr Hr Hmatch. (* r comes from the transformation *)
  clear Hmatch. (* Hmatch is not used for this proof *)
  destruct_rule Hr; (* case analysis on rules *)
    destruct_pattern Hinst sp. (* retrieve the source pattern for each rule *)
  - (* Class2Table *) specialize (H0 se). crush.
  - (* Attribute2Column *) specialize (H0 se). crush.
Qed.

*)
