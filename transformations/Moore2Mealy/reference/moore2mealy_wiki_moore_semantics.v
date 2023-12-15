(** For reference only, no CoqTL inside. *)

(*
 * In this file, I try a different fix for moore semantics.
 * Changes: 
 * - use record to represent data structures
 * - use Scheme Equality to generate X_beq, internal_X_dec
 * - change semantics of moore machine according to wiki,
     i.e. output current node, then take inputs
 * - reformulate compilation correctness theorem
 * - some naming conventions in this file
     1) surfix xM for mealy machine
     2) mkX for constructors
     3) use ' symbol to represent a tailing list
     4) library function/lemma are prefixed

 *)


Require Import List.
Require Import Coq.Arith.EqNat.
Require Import Bool.
Require Import Psatz.

(** * Moore machine *)

(* Node: 
   id x output *)

Record Node := mkNode
{ id : nat ; output : nat }.

Scheme Equality for Node.

(* Input pair: 
   src node x input *)

Record IPair := mkIPair
{ src : Node ; input : nat }.

Scheme Equality for IPair.

(* Transition rule in a moore machine: 
   Input pair x trg node *)

Record R := mkR
{ ipair : IPair ; trg : Node }.

(* Moore machine: 
   list of transition rules *)

Definition P := list R.

(* Search: 
   search corresponding target node
   for a given input pair in a moore machine *)

Fixpoint search (p: P) (ip: IPair) : option Node :=
  match p with
  | nil => None
  | r :: rs => 
      if IPair_beq (ipair r) ip 
      then 
        Some (trg r)
      else 
        search rs ip
  end.

(* Semantics of moore machine *)

Fixpoint eval (p: P) (src: Node) (I: list nat) : list nat :=
  (output src) ::
    match I with 
    | nil => nil
    | i :: I' => 
      match search p (mkIPair src i) with
      | None => nil 
      | Some trg => eval p trg I'  
      end
    end.

(** * Mealy machine *)

(* Output pair: 
   trg node x output *)

Record OPairM := mkOPairM
{ trgM : Node ; outputM : nat }.

(* Transition rule of mealy machine: 
   Input pair x Output pair *)

Record RM := mkRM
{ ipairM: IPair ; opairM: OPairM }.

(* Mealy machine *)

Definition PM := list RM.

(* Search: 
   search corresponding output pair
   for a given input pair in a mealy machine *)

Fixpoint searchM (p: PM) (i: IPair) : option OPairM :=
  match p with
  | nil => None
  | r :: rs => 
      if IPair_beq (ipairM r) i
      then 
        Some (opairM r)
      else 
        searchM rs i
end.

(* Semantics of mealy machine *)

Fixpoint evalM (p: PM) (src: Node) (I: list nat) : list nat :=
  match I with 
  | nil => nil
  | i :: I' => 
      match searchM p (mkIPair src i) with
      | None => nil
      | Some opair => (outputM opair) :: evalM p (trgM opair) I'  
      end
  end.

(** * Compiler *)

(* Compile rule *)

Definition compile_rule (r: R) := 
  let i := (ipair r) in
    let n := (trg r) in
      let o := (output (src i)) in 
  (mkRM i (mkOPairM n o)).

(* Compile machine *)

Definition compile : P -> PM := 
  List.map compile_rule.

(* Lemma: when input pair is not matched by the moore machine, 
   it is also not matched by the compiled mealy machine *)

Lemma compile_correct_ca1:
  forall p i,
     search p i = None ->
     searchM (compile p) i = None.
Proof.
  intros p i s_of_P.
  induction p as [ | r]; simpl in s_of_P; simpl.
  - reflexivity.
  - destruct (IPair_beq (ipair r) i).
    + discriminate s_of_P.
    + auto.
Qed.
  
(* Lemma: when input pair is matched by the moore machine, 
   it is also matched by the compiled mealy machine 
   their matched outputs are also a correspondence *)

Lemma compile_correct_ca2:
  forall (p: P) i a b,
    search p i = Some (mkNode a b) ->
    searchM (compile p) i = 
    Some (mkOPairM (mkNode a b) (output (src i))).
Proof.
  intros p i a b s_of_P.
  induction p as [ | r P]; simpl in s_of_P; simpl.
  - discriminate s_of_P.
  - destruct (IPair_beq (ipair r) i) eqn: ip_eq.
    + inversion s_of_P as [trg_id].
      rewrite trg_id. simpl. 
      apply internal_IPair_dec_bl in ip_eq.
      congruence.
    + auto.
Qed.

(* Lemma: when input pair is matched by the mealy machine, 
   its output corresponds to the output input pair *)

Lemma compile_correct_ca3:
  forall (p: P) src input trgM outputM,
    searchM (compile p) (mkIPair src input) = 
    Some (mkOPairM trgM outputM) ->
    outputM = output src.
Proof.
  intros p src input trgM outputM Hs.
  induction p as [ | r P].
  - simpl in Hs; inversion Hs.
  - simpl in Hs.
    destruct (IPair_beq (ipair r) {| src := src; input := input |}) eqn: ip_eq.
    + inversion Hs.
      apply internal_IPair_dec_bl in ip_eq.
      rewrite ip_eq; simpl; reflexivity.
    + specialize (IHP Hs).
      assumption.
Qed.


(* Lemma: the output of moore machine is always gt 0 *)

Lemma moore_output_length:
forall (p: P) (q0: Node) (I: list nat),
  List.length (eval p q0 I) > 0.
Proof.
  intros p q0 I.
  destruct I as [ | S_I] ; simpl eval.
  - auto.
  - apply Arith_prebase.gt_Sn_O_stt.
Qed.

(* Theorem: the output length of mealy machine 
  is always one shorter than its corresponding moore machine *)

Theorem compile_correct_output_length:
  forall (p: P) (q0: Node) (I: list nat),
    List.length (eval p q0 I) - 1 = 
    List.length (evalM (compile p) q0 I).
Proof.
  intros p q0 I. revert q0.
  induction I as [ | i I ].
  - simpl. reflexivity.
  - simpl. intro.
    destruct (search p (mkIPair q0 i)) as [ n | ] eqn: s_of_P.
    + (* input pair is matched by moore machine *)
      destruct n.
      replace (searchM (compile p) (mkIPair q0 i)) with (Some (mkOPairM (mkNode id0 output0) 
      (output (src (mkIPair q0 i)))
      )).
      * simpl.
        remember (mkNode id0 output0) as qn.
        specialize (IHI qn).
        rewrite PeanoNat.Nat.sub_1_r in IHI.
        rewrite <- IHI.
        rewrite PeanoNat.Nat.succ_pred_pos.
        rewrite Arith_prebase.minus_n_O_stt.
        reflexivity.
        apply moore_output_length.
      * symmetry. apply compile_correct_ca2. assumption.
    + (* input pair is not matched by moore machine *)
      replace (searchM (compile p) (mkIPair q0 i)) with (@None OPairM).
      * reflexivity.
      * symmetry ; apply compile_correct_ca1. assumption.
Qed.

(* main theorem: compile is correct:
   given the same inputs
   every output of mealy machine is the same as
   its corresponding moore machine *)

Theorem compile_correct:
  forall (p: P) (q0: Node) (I: list nat) (n: nat),
    n < List.length (evalM (compile p) q0 I) -> 
    nth n (eval p q0 I) 0  = 
    nth n (evalM (compile p) q0 I) 0.
Proof.
  intros p q0 I. revert q0.
  induction I as [ | i I ].
  - (* I = nil *)
    intros q0 n hL. simpl in hL. inversion hL.
  - (* I = i :: I /\ P(I') *) 
    intros q0 n hL.
    destruct (search p (mkIPair q0 i)) as [ nd | ] eqn: s_of_P.
    + (* input pair is matched by moore machine *)
      simpl evalM in hL.
      simpl evalM.
      simpl eval.
      rewrite s_of_P.
      destruct nd.
      apply compile_correct_ca2 in s_of_P.
      rewrite s_of_P.
      simpl.
      destruct n.
      * (* n = 0, the first output *)
        apply compile_correct_ca3 in s_of_P.
        symmetry. assumption.
      * (* n = S m, inductively prove the rest of output *)
        rewrite s_of_P in hL.
        simpl in hL.
        remember {| id := id0; output := output0 |} as nd.
        apply Arith_prebase.lt_S_n_stt in hL.
        specialize (IHI nd n hL).
        assumption.
    + (* input pair is not matched by moore machine *)
      simpl; simpl in hL.
      destruct (searchM (compile p) (mkIPair q0 i)) eqn: s_of_PM.
      * apply compile_correct_ca1 in s_of_P.
        rewrite s_of_P in s_of_PM.
        inversion s_of_PM.
      * inversion hL.
Qed.

