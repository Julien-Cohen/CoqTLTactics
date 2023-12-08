Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Bool.
Require Import core.Metamodel.

Require Import core.utils.Utils.
Require Import core.Model.

(* Binary Decision Diagram (Tree) *)

Inductive BDDNode := 
  BuildBDDNode :
  (* name *) string ->
  BDDNode.

Inductive BDDEdge := 
  BuildBDDEdge :
  (* child *) BDDNode ->
  (* parent *) BDDNode ->
  BDDEdge.

Scheme Equality for BDDNode.

Definition BDDM : Metamodel :=
{|
  ElementType := BDDNode;
  LinkType := BDDEdge;
  elements_eq_dec := BDDNode_eq_dec ;
|}.
