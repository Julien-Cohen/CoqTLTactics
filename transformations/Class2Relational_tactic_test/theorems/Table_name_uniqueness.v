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

Require Import transformations.Class2Relational_tactic_test.Class2Relational_tactic_test.
Require Import transformations.Class2Relational_tactic_test.ClassMetamodel.
Require Import transformations.Class2Relational_tactic_test.RelationalMetamodel.

        


Theorem Table_name_uniqueness:
forall (cm : ClassModel) (rm : RelationalModel), 
(* transformation *) 
    rm = execute Class2Relational_tactic_test cm ->
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
    (* track t1 *)
    destruct (Tactics.destruct_in_modelElements_execute_lem IN1) 
      as (r & sp & n & ope & IN_E & IN_RULE & MATCH_GUARD & IN_IT & IN_OP & IN1');
    Tactics.progress_in_In_rules IN_RULE;
    Tactics.progress_in_ope IN_OP;
    Tactics.exploit_evalGuard MATCH_GUARD;
    Tactics.exploit_evaloutpat IN1';
    Tactics.exploit_in_it IN_IT;
    Semantics.exploit_in_allTuples IN_E;
    (* track t2 *)
    destruct (Tactics.destruct_in_modelElements_execute_lem IN2) 
    as (r & sp & n & ope & IN_E2 & IN_RULE2 & MATCH_GUARD2 & IN_IT2 & IN_OP2 & IN2');
    Tactics.progress_in_In_rules IN_RULE2;
    Tactics.progress_in_ope IN_OP2;
    Tactics.exploit_evalGuard MATCH_GUARD2;
    Tactics.exploit_evaloutpat IN2';
    Tactics.exploit_in_it IN_IT2;
    Semantics.exploit_in_allTuples IN_E2;
    simpl;
    apply PRE ; auto;
    contradict D; subst; reflexivity.
Qed.

