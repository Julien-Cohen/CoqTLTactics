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


Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

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


  (* Simple logic ----------------------------------------------------------------------- *)
  intros cm rm E.
  subst rm.
  intro PRE.


(* STATE //////////////////////////////////////////////////////////////////////////////////

1 goal
cm : ClassModel
PRE : forall c1 c2 : Class_t,
      In (ClassElement c1) (modelElements cm) ->
      In (ClassElement c2) (modelElements cm) -> c1 <> c2 -> Class_name c1 <> Class_name c2
______________________________________(1/1)
forall t1 t2 : Table_t,
In (TableElement t1) (modelElements (execute Class2Relational cm)) ->
In (TableElement t2) (modelElements (execute Class2Relational cm)) ->
t1 <> t2 -> Table_name t1 <> Table_name t2

*)


  (* Simple logic ----------------------------------------------------------------------- *)
  intros t1 t2 IN1 IN2 D. 

  
(* STATE //////////////////////////////////////////////////////////////////////////////////
1 goal
cm : ClassModel
PRE : forall c1 c2 : Class_t,
      In (ClassElement c1) (modelElements cm) ->
      In (ClassElement c2) (modelElements cm) -> c1 <> c2 -> Class_name c1 <> Class_name c2
t1, t2 : Table_t
IN1 : In (TableElement t1) (modelElements (execute Class2Relational cm))
IN2 : In (TableElement t2) (modelElements (execute Class2Relational cm))
D : t1 <> t2
______________________________________(1/1)
Table_name t1 <> Table_name t2

*)


  (* Unfoldings ------------------------------------------------------------------------- *)
  destruct t1 ; destruct t2.
  unfold RelationalMetamodel.Table_name.
 

(* STATE //////////////////////////////////////////////////////////////////////////////////

1 goal
cm : ClassModel
PRE : forall c1 c2 : Class_t,
      In (ClassElement c1) (modelElements cm) ->
      In (ClassElement c2) (modelElements cm) -> c1 <> c2 -> Class_name c1 <> Class_name c2
t1, t2 : Table_t
IN1 : In (TableElement t1) (modelElements (execute Class2Relational cm))
IN2 : In (TableElement t2) (modelElements (execute Class2Relational cm))
D : t1 <> t2
______________________________________(1/1)
Table_name t1 <> Table_name t2

*)


  (* Our tactics ----------------------------------------------------------------------- *)
  TacticsBW.exploit_element_in_result IN1 ; [].
  TacticsBW.exploit_element_in_result IN2 ; [].

  
(* STATE

1 goal
cm : ClassModel
PRE : forall c1 c2 : Class_t,
      In (ClassElement c1) (modelElements cm) ->
      In (ClassElement c2) (modelElements cm) -> c1 <> c2 -> Class_name c1 <> Class_name c2
e : denoteEDatatype Class_K
IN_ELTS0 : In (ClassElement e) (modelElements cm)
e0 : denoteEDatatype Class_K
IN_ELTS1 : In (ClassElement e0) (modelElements cm)
D : {| Table_id := Class_id e; Table_name := Class_name e |} <>
    {| Table_id := Class_id e0; Table_name := Class_name e0 |}
______________________________________(1/1)
Class_name e <> Class_name e0

*)


  (* Unfoldings ------------------------------------------------------------------------- *)
  unfold denoteEDatatype in e, e0 ; simpl in e, e0.


(* STATE //////////////////////////////////////////////////////////////////////////////////

1 goal
cm : ClassModel
PRE : forall c1 c2 : Class_t,
      In (ClassElement c1) (modelElements cm) ->
      In (ClassElement c2) (modelElements cm) -> c1 <> c2 -> Class_name c1 <> Class_name c2
e : Class_t
IN_ELTS0 : In (ClassElement e) (modelElements cm)
e0 : Class_t
IN_ELTS1 : In (ClassElement e0) (modelElements cm)
D : {| Table_id := Class_id e; Table_name := Class_name e |} <>
    {| Table_id := Class_id e0; Table_name := Class_name e0 |}
______________________________________(1/1)
Class_name e <> Class_name e0

*)


  (* Apply uniqueness property in class world ------------------------------------------- *)
  eapply PRE ; [ exact IN_ELTS0 | exact IN_ELTS1 | ].


(* STATE //////////////////////////////////////////////////////////////////////////////////

1 goal
cm : ClassModel
PRE : forall c1 c2 : Class_t,
      In (ClassElement c1) (modelElements cm) ->
      In (ClassElement c2) (modelElements cm) -> c1 <> c2 -> Class_name c1 <> Class_name c2
e : Class_t
IN_ELTS0 : In (ClassElement e) (modelElements cm)
e0 : Class_t
IN_ELTS1 : In (ClassElement e0) (modelElements cm)
D : {| Table_id := Class_id e; Table_name := Class_name e |} <>
    {| Table_id := Class_id e0; Table_name := Class_name e0 |}
______________________________________(1/1)
e <> e0
*)


  (* simple logic -----------------------------------------------------------------------*)
  contradict D. subst ; reflexivity.


(* STATE //////////////////////////////////////////////////////////////////////////////////

All goals completed.

*)

Qed.

