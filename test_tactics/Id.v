(** Identifiers for nodes. *)

Require Import String.

Inductive NodeId : Set := Id : string -> NodeId.
Scheme Equality for NodeId.
