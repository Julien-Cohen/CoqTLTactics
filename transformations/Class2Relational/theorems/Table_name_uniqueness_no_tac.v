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
  apply -> SemanticsTools.in_modelElements_inv in IN1.
  apply -> SemanticsTools.in_modelElements_inv in IN2.
  destruct IN1 as (s1 & i1 & n1 & p1 & IN_EXPL1). 
  destruct IN2 as (s2 & i2 & n2 & p2 & IN_EXPL2). 
  apply  SemanticsTools.in_compute_trace_inv_right in IN_EXPL1.
  apply  SemanticsTools.in_compute_trace_inv_right in IN_EXPL2.
  destruct IN_EXPL1
        as (IN_ELTS1 & _ & r1 & IN_RULE1 & MATCH_GUARD1 
            & IN_IT1 & opu1 & IN_OUTPAT1 & EV1).
  destruct IN_EXPL2
        as (IN_ELTS2 & _ & r2 & IN_RULE2 & MATCH_GUARD2 
            & IN_IT2 & opu2 & IN_OUTPAT2 & EV2).
  simpl Syntax.rules in IN_RULE1, IN_RULE2. 
  progress repeat ListUtils.unfold_In_cons IN_RULE1 ; progress repeat ListUtils.unfold_In_cons IN_RULE2 ; [ | | | ] ;
   subst r1 ; subst r2 ;
   simpl in MATCH_GUARD1, IN_IT1, MATCH_GUARD2, IN_IT2 ;
  autounfold with parse in IN_OUTPAT2, IN_OUTPAT1 ;
  autounfold with 
         ConcreteRule_accessors ConcreteOutputPatternUnit_accessors parse rule_accessors in * ;
        unfold List.map in * ;
    progress repeat unfold_In_cons IN_OUTPAT1 ;
    progress repeat unfold_In_cons IN_OUTPAT2 ; [ | | | ].

   + 
    (* make opu appear *)
    PropUtils.inj IN_OUTPAT1.   
    PropUtils.inj IN_OUTPAT2.   

    (* make s1 and s2 appear *)
    ConcreteExpressionTools.inv_makeElement EV1.
    ConcreteExpressionTools.inv_makeElement EV2.


    (* transform incl into In *)
    repeat ListUtils.explicit_incl IN_ELTS1. 
    repeat ListUtils.explicit_incl IN_ELTS2. 


    (* Can apply PRE *)
    eapply PRE ; [ exact IN_ELTS0 | exact IN_ELTS1 | ].
    congruence.
  
  +
    PropUtils.inj IN_OUTPAT2.     
    ConcreteExpressionTools.inv_makeElement EV2.

 +
    PropUtils.inj IN_OUTPAT1.     
    ConcreteExpressionTools.inv_makeElement EV1.

 +
    PropUtils.inj IN_OUTPAT2.     
    ConcreteExpressionTools.inv_makeElement EV2.


Qed.

