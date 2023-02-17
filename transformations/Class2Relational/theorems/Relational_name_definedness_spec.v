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

From transformations.Class2Relational 
  Require C2RTactics.

Theorem Relational_name_definedness_alt_proof (te: TransformationEngine CoqTLSyntax) (cm : ClassModel) (rm : RelationalModel) :
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


  (* (1) *)
  destruct (Tactics.destruct_in_modelElements_execute_lem IN) 
    as (r & sp & n & ope & IN_E & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & IN'). 

  (* (2) *)
  Tactics.progress_in_In_rules IN_RULE ; [ | ];

  (* (3) *)
  Tactics.progress_in_ope IN_OP ;

  (* (4) *)
  Tactics.exploit_evalGuard MATCH_GUARD ;

  (* (5.E) *)  
  Tactics.exploit_evaloutpat IN' ;

  (* (6) *)
  clear IN_IT ;

  (* (7) *)
  Semantics.exploit_in_allTuples IN_E.

  {
    apply P in IN_E.
    apply IN_E.
  }
  {
    apply P in IN_E.
    apply IN_E.
  }
Qed.




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
  


