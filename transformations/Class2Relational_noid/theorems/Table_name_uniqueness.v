(**
 CoqTL user theorem: Table_name_uniqueness
 Def: if all classes in the source model have unique name,
      then the target tables generated in the target model
      have unique name.
 **)


Require Import Coq.Arith.EqNat.
Require Import List.
Require Import String.
Require Import core.utils.Utils.

Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require        usertools.TacticsBW.


Require Import transformations.Class2Relational_noid.Class2Relational.
Require Import transformations.Class2Relational_noid.ClassMetamodel.
Require Import transformations.Class2Relational_noid.RelationalMetamodel.

From transformations.Class2Relational_noid 
  Require C2RTactics.



Theorem Table_name_uniqueness :
forall (cm : ClassModel) (rm : RelationalModel), 
(* transformation *) 
    rm = execute Class2Relational cm ->
(* precondition *)   
(forall (c1: Class_t) (c2: Class_t), 
    In (ClassElement c1) cm.(modelElements) -> 
    In (ClassElement c2) cm.(modelElements) -> 
    c1 <> c2 -> 
    Class_name c1 <> Class_name c2) ->
(* postcondition *)  
(forall (t1: Table_t) (t2: Table_t), 
    In (TableElement t1) rm.(modelElements) -> 
    In (TableElement t2) rm.(modelElements) -> 
    t1 <> t2 -> 
    Table_name t1 <> Table_name t2).
Proof.
  intros cm rm E PRE t1 t2 IN1 IN2 D.
  subst rm.

  TacticsBW.exploit_element_in_result IN1 ; [].
  TacticsBW.exploit_element_in_result IN2 ; [].

  simpl in *.
  
  eapply PRE ; eauto.
  contradict D ; subst ; reflexivity.
Qed.

