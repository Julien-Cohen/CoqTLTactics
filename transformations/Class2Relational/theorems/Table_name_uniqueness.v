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

From transformations.Class2Relational 
  Require 
    ClassMetamodel 
    RelationalMetamodel 
    Class2Relational.

Import Class2Relational ClassMetamodel RelationalMetamodel.

From transformations.Class2Relational 
  Require C2RTactics.



Theorem name_uniqueness_preservation :

forall (cm : ClassModel) (rm : RelationalModel), 

(* transformation *) 
    rm = execute Class2Relational cm ->

(* precondition *)   
( forall (c1: Class_t) (c2: Class_t), 
    In (ClassElement c1) cm.(modelElements) -> 
    In (ClassElement c2) cm.(modelElements) -> 
    c1 <> c2 -> 
    Class_name c1 <> Class_name c2
) ->

(* postcondition *)  
( forall (t1: Table_t) (t2: Table_t), 
    In (TableElement t1) rm.(modelElements) -> 
    In (TableElement t2) rm.(modelElements) -> 
    t1 <> t2 -> 
    Table_name t1 <> Table_name t2
).

Proof.

  (* Simple logic ------------------------------------ *)
  intros cm rm E. subst rm. intro PRE.

  (* Simple logic ------------------------------------ *)
  intros t1 t2 IN1 IN2 D. 
  
  (* Unfoldings -------------------------------------- *)
  destruct t1 ; destruct t2.
  unfold RelationalMetamodel.Table_name.
 
  (* Our tactics ------------------------------------- *)
  TacticsBW.exploit_element_in_result IN1 ; [].
  TacticsBW.exploit_element_in_result IN2 ; [].
  
  (* Unfoldings -------------------------------------- *)
  unfold denoteEDatatype in e, e0 ; simpl in e, e0.

  (* Apply uniqueness property in class world -------- *)
  eapply PRE ; [ exact IN_ELTS0 | exact IN_ELTS1 | ].

  (* Simple logic ------------------------------------ *)
  contradict D. subst ; reflexivity.

Qed.

