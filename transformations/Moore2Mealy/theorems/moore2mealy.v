(*
 * - change the definitions of moore and mealy machine for proofs
 * - write moore2mealy model transformation use a single function
 * - prove its correctness
 *)


Require Import List.
Require Import Coq.Arith.EqNat.
Require Import Bool.

(** * Moore machine *)

(* Node: id x output *)
Inductive Node :=
 | node : nat -> nat -> Node.

Definition beq_N n1 n2 :=
  match n1, n2 with
    node id1 o1, node id2 o2 => beq_nat id1 id2 && beq_nat o1 o2
  end.

(* Input pair: src node x input *)
Inductive IPair :=
 | Ipr : Node -> nat -> IPair.

Definition beq_IPair p1 p2 :=
  match p1, p2 with
    Ipr n1 i1, Ipr n2 i2 => beq_N n1 n2 && beq_nat i1 i2
  end.

(* Transition rule of moore machine: Input pair x trg node *)
Inductive R :=
 | r : IPair -> Node -> R.


(* moore machine *)
Definition P := list R.

(* search output node in moore machine *)
Fixpoint search (p: P) (i: IPair) : option Node :=
  match p with
  | nil => None
  | (r a b) :: rs => 
      if beq_IPair a i 
      then 
        Some b 
      else 
        search rs i 
  end.

(* semantics of moore machine  *)
Fixpoint eval (p: P) (q0: Node) (I: list nat) : list nat :=
  match I with 
  | nil => nil
  | i :: I' => 
      
      match search p (Ipr q0 i) with
      | None => nil (* error ? *)
      | Some (node a b) => b :: eval p (node a b) I'  
      end
  end.

(** * Mealy machine *)

(* Output pair: trg node x output *)
Inductive OPair :=
 | Opr : Node -> nat -> OPair.


(* Transition rule of mealy machine : Input pair x trg node *)
Inductive R' :=
 | r' : IPair -> OPair -> R'.

(* mealy machine *)
Definition P' := list R'.

(* search output node *)
Fixpoint search' (p: P') (i: IPair) : option OPair :=
  match p with
  | nil => None
  | r' a b :: rs => 
      if beq_IPair a i 
      then 
        Some b 
      else 
        search' rs i 
end.

(* semantics of mealy machine *)
Fixpoint eval' (p: P') (q0: Node) (I: list nat) : list nat :=
  match I with 
  | nil => nil
  | i :: I' => 
      match search' p (Ipr q0 i) with
      | None => nil
      | Some (Opr a b) => b :: eval' p a I'  
      end
  end.

(** * compiler *)

(* compile moore to mealy *)

Definition compile_rule t := 
  match t with 
    r a (node c d) => r' a (Opr (node c d) d) 
  end.

Definition compile : P -> P' := List.map compile_rule.

(* Lemma: when input pair is not matched by moore machine, 
   it is also not matched by the compiled mealy machine *)
Lemma compile_s_correct_ca1:
  forall (p: P) i,
     search p i = None ->
     search' (compile p) i = None.
Proof.
  intros p i s_of_P.
  induction p; simpl in s_of_P; simpl.
  - reflexivity.
  - destruct a. destruct n. simpl.
    destruct (beq_IPair i0 i).
    + discriminate s_of_P.
    + auto.
Qed.



(* Lemma: when input pair is matched by moore machine, 
   it is also matched by the compiled mealy machine 
   their matched outputs are also a correspondence *)
Lemma compile_s_correct_ca2:
  forall (p: P) i a b,
    search p i = Some (node a b) ->
    search' (compile p) i = Some (Opr (node a b) b).
Proof.
  intros p i a b s_of_P.
  induction p; simpl in s_of_P; simpl.
  - discriminate s_of_P.
  - destruct a0. destruct n. simpl. 
    destruct (beq_IPair i0 i).
    + congruence. 
    + auto.
Qed.

(* main theorem: compile is correct
   evaluation the same inputs produce the same output *)
Theorem compile_correct:
  forall (p: P) (q0: Node) (I: list nat),
    eval p q0 I = eval' (compile p) q0 I.
Proof.
  intros p q0 I. revert q0.
  induction I as [ | i I ].
  - (* I = nil *)
    intro ; reflexivity.
  - (* I = i :: I /\ P(I') *) 
    simpl. intro.
    destruct (search p (Ipr q0 i)) as [ n | ] eqn: s_of_P.
    + (* input pair is matched by moore machine *)
      destruct n.
      replace (search' (compile p) (Ipr q0 i)) with (Some (Opr (node n n0) n0)).
      * f_equal ; auto.
      * symmetry ; apply compile_s_correct_ca2. assumption. 
    + (* input pair is not matched by moore machine *)
      replace (search' (compile p) (Ipr q0 i)) with (@None OPair).
      * reflexivity.
      * symmetry ; apply compile_s_correct_ca1. assumption.
Qed.

