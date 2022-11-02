(*
 * - change the definitions of moore and mealy machine for proofs
 * - write moore2mealy model transformation use a single function
 * - prove its correctness
 *)


Require Import List.
Require Import Coq.Arith.EqNat.
Require Import Bool.

(** Moore machine *)

(* Node: id x output *)
Inductive N :=
| n : nat -> nat -> N.

Definition N_id n0 := match n0 with n id o => id end. 
Definition N_o n0 := match n0 with n id o => o end.
Definition beq_N n1 n2 :=
match n1, n2 with
n id1 o1, n id2 o2 => beq_nat id1 id2 && beq_nat o1 o2
end.

(* Input pair: src node x input *)
Inductive IPair :=
| Ipr : N -> nat -> IPair.

Definition beq_IPair p1 p2 :=
match p1, p2 with
Ipr n1 i1, Ipr n2 i2 => beq_N n1 n2 && beq_nat i1 i2
end.

(* Transition rule of moore machine: Input pair x trg node *)
Inductive R :=
| r : IPair -> N -> R.

Definition R_Ip r0 := match r0 with r Ip0 n0 => Ip0 end. 
Definition R_n r0 := match r0 with r Ip0 n0 => n0 end.


(* moore machine *)
Definition P := list R.

(* search output node in moore machine *)
Fixpoint s (p: P) (Ip: IPair) : option N :=
match p with
| nil => None
| r0 :: rs => 
    if beq_IPair (R_Ip r0) Ip then 
        Some (R_n r0) 
    else 
        s rs Ip 
end.

(* semantics of moore machine  *)
Fixpoint eval (p: P) (q0: N) (I: list nat) : list nat :=
match I with 
| nil => nil
| i :: I' => 
let input := (Ipr q0 i) in 
    match (s p input) with
    | None => nil
    | Some oN => (N_o oN) :: eval p oN I'  
    end
end.

(** Mealy machine *)

(* Output pair: trg node x output *)
Inductive OPair :=
| Opr : N -> nat -> OPair.

Definition OPair_n Op0 := match Op0 with Opr n0 o0 => n0 end. 
Definition OPair_o Op0 := match Op0 with Opr n0 o0 => o0 end.

(* Transition rule of mealy machine : Input pair x trg node *)
Inductive R' :=
| r' : IPair -> OPair -> R'.

Definition R'_Ip r0 := match r0 with r' Ip0 Op0 => Ip0 end. 
Definition R'_Op r0 := match r0 with r' Ip0 Op0 => Op0 end.

(* mealy machine *)
Definition P' := list R'.

(* search output node *)
Fixpoint s' (p: P') (Ip: IPair) : option OPair :=
match p with
| nil => None
| r0 :: rs => 
    if beq_IPair (R'_Ip r0) Ip then 
        Some (R'_Op r0) 
    else 
        s' rs Ip 
end.

(* semantics of mealy machine *)
Fixpoint eval' (p: P') (q0: N) (I: list nat) : list nat :=
match I with 
| nil => nil
| i :: I' => 
let input := (Ipr q0 i) in 
    match (s' p input) with
    | None => nil
    | Some oP => (OPair_o oP) :: eval' p (OPair_n oP) I'  
    end
end.

(** compiler *)

(* compile moore to mealy *)
Fixpoint compile (p: P) : P' :=
match p with
| nil => nil
| rl :: rs => r' (R_Ip rl) (Opr (R_n rl) (N_o (R_n rl))) :: compile rs
end.

(* Lemma: when input pair is not matched by moore machine, 
   it is also not matched by the compiled mealy machine *)
Lemma compile_s_correct_ca1:
forall (p: P) (q0: N) (i: nat) (Ip: IPair),
(Ipr q0 i) = Ip ->
(s p Ip) = None ->
(s' (compile p) Ip) = None.
Proof.
intros p q0 i Ip input s_of_P.
induction p; simpl in s_of_P; simpl.
- auto.
- destruct (beq_IPair (R_Ip a) Ip).
  + inversion s_of_P. 
  + auto.
Qed.

(* Lemma: when input pair is matched by moore machine, 
   it is also matched by the compiled mealy machine 
   their matched outputs are also a correspondence *)
Lemma compile_s_correct_ca2:
forall (p: P) (q0: N) (i: nat) (Ip: IPair) (n: N),
(Ipr q0 i) = Ip ->
(s p Ip) = Some n ->
(s' (compile p) Ip) = Some (Opr n (N_o n)).
Proof.
intros p q0 i Ip n input s_of_P.
induction p; simpl in s_of_P; simpl.
- inversion s_of_P.
- destruct (beq_IPair (R_Ip a) Ip).
  + inversion s_of_P as [id]. rewrite id. auto.
  + auto.
Qed.

(* main theorem: compile is correct
   evaluation the same inputs produce the same output *)
Theorem compile_correct:
forall (p: P) (q0: N) (I: list nat),
    eval p q0 I = eval' (compile p) q0 I.
Proof.
intros p q0 I. revert q0.
induction I as [|i].
- (* I = nil *)
  simpl. auto.  
- (* I = i :: I /\ P(I') *) 
  simpl. intro.
  remember (Ipr q0 i) as input.
  destruct (s p input) as [n|] eqn: s_of_P.
  + (* input pair is matched by moore machine *)
    assert ((s' (compile p) input) = Some (Opr n (N_o n))).
    { specialize (compile_s_correct_ca2 p q0 i input). auto. }
    rewrite H. simpl.
    specialize (IHI n). rewrite IHI. auto.
  + (* input pair is not matched by moore machine *)
    assert ((s' (compile p) input) = None).
    { specialize (compile_s_correct_ca1 p q0 i input). auto. }
    rewrite H. auto.
Qed.

