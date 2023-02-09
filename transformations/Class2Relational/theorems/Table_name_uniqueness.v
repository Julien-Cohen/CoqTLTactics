(**
 CoqTL user theorem: Table_name_uniqueness
 Def: if all classes in the source model have unique name,
      then the target tables generated in the target model
      have unique name.
 **)

Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import String.
Require Import core.utils.Utils.

Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

From transformations.Class2Relational 
  Require C2RTactics.



Theorem Table_name_uniqueness_alt_proof:
forall (cm : ClassModel) (rm : RelationalModel), 
(* transformation *) 
    rm = execute Class2Relational cm ->
(* precondition *)   
(forall (c1: Class_t) (c2: Class_t), 
    In (ClassElement c1) cm.(modelElements) -> 
    In (ClassElement c2) cm.(modelElements) -> 
    c1 <> c2 -> 
    class_name c1 <> class_name c2) ->
(* postcondition *)  
(forall (t1: Table_t) (t2: Table_t), 
    In (TableElement t1) rm.(modelElements) -> 
    In (TableElement t2) rm.(modelElements) -> 
    t1 <> t2 -> 
    table_name t1 <> table_name t2).
Proof.
  intros cm rm E PRE t1 t2 IN1 IN2 D.
  subst rm.
  
  
  
  (* (0) *)
  Tactics.chain_destruct_in_modelElements_execute IN1.
  
  clear IN_IT.
  
  (* (1) *)
  Tactics.progress_in_In_rules IN_M ; [ |  ];
  
  (* (2) *)
  C2RTactics.progress_in_guard M ;

  (* (3) *)
  C2RTactics.progress_in_ope IN_OP ;
  
  (* (4.E) *)
  C2RTactics.progress_in_evalOutput IN1.

  (* (0) *)
  Tactics.chain_destruct_in_modelElements_execute IN2.

  clear IN_IT.

  (* (1) *)
  Tactics.progress_in_In_rules IN_M ; [ |  ];
  
  (* (2) *)
  C2RTactics.progress_in_guard M ;

  (* (3) *)
  C2RTactics.progress_in_ope IN_OP ;
  
  (* (4.E) *)
  C2RTactics.progress_in_evalOutput IN2.

  simpl in *.
  
  repeat Tactics.in_singleton_allTuples_auto.
  eapply PRE ; eauto.
  contradict D ; subst ; reflexivity.
Qed.

Theorem Table_name_uniqueness:
forall (cm : ClassModel) (rm : RelationalModel), 
(* transformation *) 
    rm = execute Class2Relational cm ->
(* precondition *)   
(forall (c1: Class_t) (c2: Class_t), 
    In (ClassElement c1) cm.(modelElements) -> 
    In (ClassElement c2) cm.(modelElements) -> 
    c1 <> c2 -> 
    class_name c1 <> class_name c2) ->
(* postcondition *)  
(forall (t1: Table_t) (t2: Table_t), 
    In (TableElement t1) rm.(modelElements) -> 
    In (TableElement t2) rm.(modelElements) -> 
    t1 <> t2 -> 
    table_name t1 <> table_name t2).
Proof.
    intros cm rm E PRE t1 t2 IN1 IN2 D.
    subst rm.

    repeat Tactics.destruct_execute.

    repeat Tactics.show_singleton.

    repeat C2RTactics.show_origin.

    repeat C2RTactics.unify_all.

    simpl in *.

    repeat Tactics.in_singleton_allTuples_auto.
    eapply PRE ; eauto.
    contradict D ; subst ; reflexivity.
Qed.

