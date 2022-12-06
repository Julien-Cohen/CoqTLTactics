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

Definition BDDEq (a b : BDDNode) := 
  match a, b with
  | BuildBDDNode n1, BuildBDDNode n2 => String.eqb n1 n2 
  end.

Definition BDDEdege_beq a b :=
  match (a,b) with
    | (BuildBDDEdge n1 n2, BuildBDDEdge n3 n4) => BDDEq n1 n3 && BDDEq n1 n4
  end.

Definition BDDM : Metamodel :=
{|
  ModelElement := BDDNode;
  ModelLink := BDDEdge;
  elements_eqdec := BDDEq ;
  links_eqdec :=  BDDEdege_beq
|}.
