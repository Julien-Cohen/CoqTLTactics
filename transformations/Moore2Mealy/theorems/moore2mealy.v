(*
 * - change the definitions of moore and mealy machine for proofs
 * - write moore2mealy model transformation use a single function
 * - prove its correctness
 *)


Require Import List.
Require Import Coq.Arith.EqNat.
Require Import Bool.

Require PropUtils.

Module Moore.
(** * Moore machine *)

(* Node: id x output *)
Record Node := { id : nat ; output : nat }.

Definition beq_N n1 n2 :=
    beq_nat n1.(id) n2.(id) && beq_nat n1.(output) n2.(output).

(* Input pair: src node x input *)
Definition IPair : Set := Node * nat.

Definition beq_IPair p1 p2 :=
  match p1, p2 with
    (n1, i1), (n2, i2) => beq_N n1 n2 && beq_nat i1 i2
  end.

(* Transition rule of moore machine: Input pair x trg node *)
Definition R :Set := IPair * Node.


(* moore machine *)
Definition P := list R.

(* search output node in moore machine *)
Fixpoint search (p: P) (i: IPair) : option Node :=
  match p with
  | nil => None
  | (a, b) :: rs => 
      if beq_IPair a i 
      then 
        Some b 
      else 
        search rs i 
  end.

(* semantics of moore machine  *)
Fixpoint eval (p: P) (q0: Node) (I: list nat) : option (list nat) :=
  match I with 
  | nil => Some nil
  | i :: I' => 
      
      match search p (q0, i) with
      | None => None 
      | Some (Build_Node a b) => 
          (*res <- eval p (node a b) I' ; return res*)
          match eval p (Build_Node a b) I' with 
          | Some res => Some (b :: res) 
          | None => None
          end 
      end
  end.

End Moore.

Module Mealy.
(** * Mealy machine *)

(* Output pair: trg node x output *)
Definition OPair : Set := Moore.Node * nat. (* FIXME *)


(* Transition rule of mealy machine : Input pair x trg node *)
Definition R : Set := Moore.IPair * OPair.

(* mealy machine *)
Definition P := list R.

(* search output node *)
Fixpoint search (p: P) (i: Moore.IPair) : option OPair :=
  match p with
  | nil => None
  | (a, b) :: rs => 
      if Moore.beq_IPair a i 
      then 
        Some b 
      else 
        search rs i 
end.

(* semantics of mealy machine *)
Fixpoint eval (p: P) (q0: Moore.Node) (I: list nat) : option (list nat) :=
  match I with 
  | nil => Some nil
  | i :: I' => 
      match search p (q0, i) with
      | None => None
      | Some (a, b) => 
          match eval p a I' with
          | Some res =>Some (b :: res)
          | None => None
          end  
      end
  end.

End Mealy.

(** * compiler *)

(* compile moore to mealy *)

Definition compile_rule (t:Moore.R) : Mealy.R := 
  match t with 
    (a, n) => (a, (n, n.(Moore.output))) 
  end.

Definition compile : Moore.P -> Mealy.P := 
  List.map compile_rule.

(* Lemma: when input pair is not matched by moore machine, 
   it is also not matched by the compiled mealy machine *)
Lemma compile_s_correct_ca1:
  forall (p: Moore.P) i,
     Moore.search p i = None ->
     Mealy.search (compile p) i = None.
Proof.
  intros p i s_of_P.
  induction p; simpl in s_of_P; simpl.
  - reflexivity.
  - destruct a. destruct n. simpl.
    destruct (Moore.beq_IPair i0 i).
    + discriminate s_of_P.
    + auto.
Qed.



(* Lemma: when input pair is matched by moore machine, 
   it is also matched by the compiled mealy machine 
   their matched outputs are also a correspondence *)
Lemma compile_s_correct_ca2:
  forall (p: Moore.P) i n,
    Moore.search p i = Some n ->
    Mealy.search (compile p) i = Some (n, n.(Moore.output)).
Proof.
  intros p i n s_of_P.
  induction p; simpl in s_of_P; simpl.
  - discriminate s_of_P.
  - destruct a. destruct n. simpl. 
    destruct (Moore.beq_IPair i0 i).
    + destruct n0. PropUtils.inj s_of_P. reflexivity.
    + auto.
Qed.

(* main theorem: compile is correct
   evaluation the same inputs produce the same output *)
Theorem compile_correct:
  forall (p: Moore.P) (q0: Moore.Node) (I: list nat),
    Moore.eval p q0 I = Mealy.eval (compile p) q0 I.
Proof.
  intros p q0 I. revert q0.
  induction I as [ | i I ].
  - (* I = nil *)
    intro ; reflexivity.
  - (* I = i :: I /\ P(I') *) 
    simpl. intro.
    destruct (Moore.search p (q0, i)) as [ n | ] eqn: s_of_P.
    + (* input pair is matched by moore machine *)
      destruct n.
      replace (Mealy.search (compile p) (q0, i)) with (Some ((Moore.Build_Node id output), output)).
      * rewrite IHI. reflexivity. 
      * symmetry ; apply compile_s_correct_ca2. assumption. 
    + (* input pair is not matched by moore machine *)
      replace (Mealy.search (compile p) (q0, i)) with (@None Mealy.OPair).
      * reflexivity.
      * symmetry ; apply compile_s_correct_ca1. assumption.
Qed.

