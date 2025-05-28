(** Identifiers for nodes. *)

From Stdlib Require Import String.

Inductive NodeId : Set := Id : string -> NodeId.
Scheme Equality for NodeId.
