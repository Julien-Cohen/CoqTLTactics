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


Theorem Relational_name_definedness (te: TransformationEngine CoqTLSyntax) (cm : ClassModel) (rm : RelationalModel) :
  (* transformation *) 
     rm = execute Class2Relational cm ->
  (* precondition *)   
     (forall (c1 : ClassMetamodel.Element), 
         In c1 cm.(modelElements) -> 
            (ClassMetamodel.getName c1 <> ""%string)) ->
  (* postcondition *) 
     (forall (e : RelationalMetamodel.Element), 
         In e rm.(modelElements) -> 
            (RelationalMetamodel.getName e <> ""%string)). 
Proof.
  intros T P e IN; intros.
  subst rm.

  Tactics.destruct_execute.

  Tactics.show_singleton. 

  Tactics.in_singleton_allTuples.
  specialize (P e0 IN_E). 
  
  destruct e0. (* Case analysis on source element type *)
  * (* [Class] *) 
    repeat Tactics.destruct_any.
    
    Tactics.destruct_In_two ;
      simpl in * ;
      remove_or_false IN_OP ;
      subst ope ; simpl in *. 
    ** (* Class2Table *)
      inversion_clear IN.
      exact P.
      
    **  (* Attribute2Column contradict *)
      exfalso.
      discriminate IN.
      
  * (* [Attribute] *) 
    destruct a.
    destruct derived ; repeat Tactics.destruct_any.
    -- (* derived *)
      exfalso. (* no rule can match *)
      Tactics.destruct_In_two ; discriminate M.

             
    -- (* not derived *) 
      Tactics.destruct_In_two;
        simpl in * ;
        remove_or_false IN_OP ;
        subst ope ; simpl in *.
      **  (* Class2Table impossible *)
        exfalso.
        discriminate IN.
        
      ** (* Attribute2Column *) 
        simpl in IN ; inversion_clear IN.
        simpl. 
        exact P.
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
  (* precondition *)   (forall (c1 : ClassMetamodel_Element), In c1 (allModelElements cm) -> (ClassMetamodel_getName c1 <> ""%string)) ->
  (* postcondition *)  (forall (t1 : RelationalMetamodel_Element), In t1 (allModelElements rm) -> (RelationalMetamodel_getName t1 <> ""%string)).
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
